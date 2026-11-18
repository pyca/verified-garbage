module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Arm.Odd
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangePre
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntryCT
import VerifiedGarbage.Proof.Ffdh.Domain

/-! ### `Ffdh.Arm.VettedValidation.RecognitionTiming`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.VettedValidation.Sat`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.OddCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ExchangeVerified`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ExchangeCorrect`, which only this module used -/

section

/-! The callable shared-secret computation satisfies the architecture-independent contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchange_data (s : State) (pre : (Spec.Ffdh.exchangeContract abi 128).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ stackArg s 3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧
      (stackArg s 0).toNat = p.k ∧ (stackArg s 6).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ ExchangeFnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := s.gpr .r2
    publicValue := stackArg s 3
    privateValue := stackArg s 1
    output := s.gpr .r0
    entropy := 0
    len := (stackArg s 6).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3 * (stackArg s 0).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 0).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    exchange_input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem exchange_correct (s : State) (pre : (Spec.Ffdh.exchangeContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.Exchange.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.exchangeContract abi 128).post s t := by
  obtain ⟨p, yb, xb, _, out, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := exchange_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := exchangeFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have lengths : (s.gpr .r1).toNat = (stackArg s 0).toNat ∧
      (stackArg s 4).toNat = (stackArg s 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, outLen, yLen, _, _, _⟩ := pre
    exact ⟨outLen, yLen⟩
  sig_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [lengths.1, lengths.2, count, domain, peer, scalar, privateCount, domainBytes,
    peerBytes, scalarBytes, out]
  intro valid validPeer
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  exact exchangeResult_spec valid validPeer (result modValid)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ExchangeContractCT`, which only this module used -/

section

/-! The shared exchange timing policy is satisfied even when private values and statuses differ. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ExchangeBodyCT.lean`, which only this module imported.
section

/-! Invalid-domain handling and the shared-secret body reveal no private scalar data. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeBody_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => ExchangeMainInput p slots yb xb1 s ∧ ExchangeMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.Exchange.main) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => ExchangeMainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => ExchangeMainInput p slots yb xb1 s ∧ ExchangeMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : ExchangeMainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, h.peer.after_frame frame rest (sourceSep h.peerStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack), h.output.after rest,
      by rw [rest.sp]; exact h.peerStack, by rw [rest.sp]; exact h.scalarStack,
      h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact saved d hd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.Exchange.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact exchangeMain_ct stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) saved'
        peerLength positive fits count length facts.2.1 facts.1 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ExchangeFnCT.lean`, which only this module imported.
section

/-! The complete callable shared-secret computation is constant time in the private scalar. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeFn_ct {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => ExchangeFnInput p yb xb1 s ∧ ExchangeFnInput p yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.code (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, ExchangeFnInput p yb xb s ∧ a = entered s
  have entry := exchangeEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) a
        (ExchangeMainInput p [0, 36, 44, 40, 32, 28, 24, 4] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (exchangeEntry_ok (entered s) input.args input.incoming input.out input.domain input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.peer.after_frame frame rest (sourceSep input.peerStack),
      input.scalar.after_frame frame rest (sourceSep input.scalarStack), input.output.after rest,
      by rw [rest.sp]; exact input.peerStack, by rw [rest.sp]; exact input.scalarStack,
      input.workspaceSep, by rw [rest.sp]; exact input.stackSep⟩
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (exchangeBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.peerLength related.1.positive related.1.scalarFit related.1.scalarCount length)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem exchange_contract_ct : ConstantTime isa (Spec.Ffdh.exchangeContract abi 128).pre
    (Spec.Ffdh.exchangeContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.Exchange.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, out, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := exchange_data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.exchangeContract abi 128).pre a) :
      (stackArg a 4).toNat = (stackArg a 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p2, ← p3, ← p7, ← p4] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, _⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := exchange_input t ht (p := p) (yb := yb) (xb := xb2)
    (p9.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p7.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p4]; exact count) (by rw [← p10]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    exact (exchangeFn_ct (by rw [xLength, x2Length]) s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p3, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 3)) (stackArg s 0).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm

end

end


/-! Native ARMv7 shared-secret computation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def exchangeSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else if a = 0x8010 then 64 else if a = 0x8015 then 0x40 else
    if a = 0x8018 then 0x20 else if a = 0x8019 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x8000, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem exchange_sat : ∃ s, (Spec.Ffdh.exchangeContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [exchangeSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using exchangeSat

theorem exchange_verified : Verified target VG.Impl.Ffdh.Arm.Domain.Exchange.code
    (Spec.Ffdh.exchangeContract abi 128) :=
  ⟨exchange_correct, exchange_contract_ct, exchange_sat⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Reading an operand's parity uses a public array pointer and fixed byte offset. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem odd_ct {base : BitVec 32} {len w a : Nat} (ha : a < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.odd a) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (.block [.ldr .r4 .r0 (64 + 8 * a)]) (fun _ _ => True) := by
    have trace : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
        (.block [.ldr .r4 .r0 (64 + 8 * a)]) (fun _ _ => True) := by
      have casesA : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega_using [ha]
      rcases casesA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)
    exact trace.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block [.ldr .r4 .r0 (64 + 8 * a)]) s
        (fun t => t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a)) := by
    have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
    have size : 64 + 8 * a + 4 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [ha, fits]
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (by omega_using [ha]) (a := off (State.addr base) (64 + 8 * a))
      (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_using [size, this]))
      (h.workspace.read size) fun t loaded => WP.block_nil ?_
    exact loaded.gpr.trans (header.array a ha)
  have tail : RelCT isa (fun s t => s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) ∧
      t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) ∧ s.sp = t.sp)
      (.block [.ldrb .r11 .r4 0, .dp .and .r11 .r11 (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.1.symm
  exact RelCT.block_append (relCT_chain load wp wp tail)

end VG.Proof.Ffdh.Arm

end

end

/-! The parameter contract has a concrete caller with the shared table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

private def attemptBase : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x20 else if a = 0x8001 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 8448⟩]

@[irreducible] private def attemptMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 W a else attemptBase.mem a

private def attemptSat (W : List (BitVec 64)) : State :=
  { attemptBase with
    mem := attemptMem W
    rd := attemptBase.rd ++ [⟨0x100000, 17744⟩]
    syms := fun _ => 0x100000 }

private theorem attemptMem_held (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (attemptMem W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x100000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold attemptMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega_using [hi, hj]

private theorem attemptSat_arg (W : List (BitVec 64)) {i : Nat} (hi : i < 1) : stackArg (attemptSat W) i = stackArg attemptBase i := by
  apply Mem.readW_congr
  intro j hj
  change attemptMem W _ = attemptBase.mem _
  unfold attemptMem
  apply ite_eq_right
  have small : ∀ i < 1, ∀ j < 4,
      ¬ (stackArgAddr attemptBase i + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small i hi j hj

private theorem satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, W)]) 128).pre s := by
  refine ⟨attemptSat W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · have args (i : Nat) (hi : i < 1) := attemptSat_arg W hi
    sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords, abi,
      argRegs, reduceClassify, Loc.val, State.addr]
    simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat), stackArg (stripConsts K s) i = stackArg s i by intros; rfl]
    simp only [args 0 (by decide)]
    dsimp only [stackArgAddr, stripConsts, State.withRegions, attemptSat, attemptBase]
    repeat' apply And.intro
    all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)
  · refine ⟨?_, ?_, ?_, fun r hr => by
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      dsimp only [symAddr, attemptSat]
      decide⟩
    · simp only [attemptSat, attemptBase, constRegs, Abi.constRegions, symAddr, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact attemptMem_held W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [symAddr, attemptSat]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x3000, 8448⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl
        all_goals first | contradiction | (apply Region.disjoint_of_sep; decide)
      · intro q hq
        simp only [abi, stackBelow, List.mem_singleton] at hq
        subst q
        exact Region.disjoint_of_sep (by decide)

theorem sat :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 128).pre s :=
  satAux tableWords VettedGroups.tableWords_length

end VG.Proof.Ffdh.Arm.VettedValidation

end

end

/-! ### `Ffdh.Arm.DomainEntryCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.PrivateVerified`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.PrivateCorrect`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivatePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.PrivateFn`, which this module and modules that import it used -/

section

/-! The native private-key check, from its entry through AAPCS restoration. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateEntry.lean`, which only this module imported.
section

/-! Retain the imported private-key ABI's public and scalar arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PrivateIncoming (p : Inputs) (s : State) : Prop where
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  scratch : IncomingWord p.base 140 s

theorem privateEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : PrivateIncoming p s) (domain : s.gpr .r0 = p.domain)
    (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length) (count : s.gpr .r2 = BitVec.ofNat 32 p.k)
    (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) s fun t =>
      Context p [0, 44, 40, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain args0 := h.of_mem moved.mem rest0
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 24 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans domain) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  obtain rest1 := rest0.trans (stepRest1.mono (by simp))
  obtain stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  obtain frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r1 28 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r1 (by simp)).trans domainLength) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  obtain rest2 := rest1.trans (stepRest2.mono (by simp))
  obtain stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  obtain frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 32 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r2 (by simp)).trans count) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  obtain rest3 := rest2.trans (stepRest3.mono (by simp))
  obtain stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  obtain frame3 := frame2.trans stepFrame3
  refine wp_store_arg .r3 36 args3 (by decide) (by decide) (by decide)
    ((rest3.gpr .r3 (by simp)).trans publicValue) stack3 fun s4 args4 stepFrame4 stepRest4 => ?_
  obtain rest4 := rest3.trans (stepRest4.mono (by simp))
  obtain stack4 := (stepRest4.gpr .r12 (by simp)).trans (stack3.trans stepRest4.sp.symm)
  rw [rest3.sp] at stepFrame4
  obtain frame4 := frame3.trans stepFrame4
  obtain allRest4 : Rest roundClobbers s s4 := rest4.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.scalar.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  obtain allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  obtain frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.scalarCount.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  obtain allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  obtain frame6 := frame5.trans stepFrame6
  refine wp_retain_incoming .r0 (by decide) args6 (by decide)
    (incoming.scratch.after (by decide) frame6 allRest6) (by decide) (by decide) (by decide) stack6
    fun s7 args7 stepFrame7 stepRest7 value7 stack7 => WP.block_nil ?_
  refine ⟨⟨args7, value7⟩, ?_⟩
  rw [allRest6.sp] at stepFrame7
  exact frame6.trans stepFrame7

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem privateEntered_ok (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : PrivateIncoming p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main)) s fun t =>
      t.gpr .r0 = checkedPrivateFlag p yb xb ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (privateEntry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  obtain valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  obtain valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  obtain scalarU := scalar.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r; exact scalarStack)
  refine WP.mono (privateBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) valueU length scalarU positive scalarLength scalarCount
    (by rw [restU.sp]; exact scalarStack) valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  obtain entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure PrivateFnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : PrivateIncoming p (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  value : Octets p.base p.publicValue p.len yb (entered s)
  length : yb.length = p.k
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem privateFn_ok (s : State) {p : Inputs} {yb xb : List Byte} (h : PrivateFnInput p yb xb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPrivateFlag p yb xb := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedPrivateFlag p yb xb) h.saved ?_
  refine WP.mono (privateEntered_ok (entered s) h.args h.incoming h.domain h.domainLength
    h.count h.publicValue h.value h.length h.scalar h.positive h.scalarLength h.scalarCount h.scalarStack h.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The shared imported-private-key signature supplies native frame and buffer invariants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem private_input (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 3 = p.base) (domain : s.gpr .r0 = p.domain) (peer : s.gpr .r3 = p.publicValue)
    (scalar : stackArg s 1 = p.privateValue) (count : (s.gpr .r2).toNat = p.k)
    (capacity : (stackArg s 4).toNat = p.len) (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    PrivateFnInput p yb xb s := by
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, xS, sArgs, stackDom, stackY, stackX, stackS, stackArgs,
    domFit, yFit, xFit, sFit, _, _, yLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have yLength : yb.length = p.k := by
    have eq := congrArg List.length peerBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [count] at xMax
  rw [privateCount] at rd xS stackX xFit xPositive xMax
  rw [domain, domLen] at rd domS stackDom domFit
  rw [peer] at rd yS stackY yFit
  rw [scalar] at rd xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS xS yS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackX stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have peerRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootPeer : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [yLength]; exact yFit, by rw [yLength]; exact peerRead,
      by rw [yLength]; exact yS, by rw [yLength]; exact peerBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets rootDomain stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]; exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      (stackArgs.sub_right (argSub i hi)) rfl
  have nativeIncoming : PrivateIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h
    · rw [← base]; exact incoming 3 (by decide)
  refine ⟨stackFit, args, nativeIncoming, domain, ?_, ?_, peer,
    entered_octets rootPeer stackFit (by rw [yLength]; exact stackY), yLength,
    entered_octets rootScalar stackFit (by rw [xLength]; exact stackX),
    by rw [xLength]; omega_using [xPositive], by rw [xLength]; exact xMax, ?_, ?_, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [xLength]; exact stackX.symm.sub_right (locals_sub_reserved s stackFit)
  · rw [yLength]; exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm

end

end

/-! Native callable imported-private-key validation satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem private_data (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧ (s.gpr .r2).toNat = p.k ∧
      (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ PrivateFnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := stackArg s 1
    output := 0
    entropy := 0
    len := (stackArg s 4).toNat
    k := (s.gpr .r2).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    private_input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem private_correct (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPrivateContract abi 128).post s t := by
  obtain ⟨p, yb, xb, _, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := private_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := privateFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have length : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := pre
    exact length
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [length, count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes]
  intro valid
  rw [result]
  exact checkedPrivateFlag_spec p yb xb valid

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.PrivateContractCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateMainCT`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateState`, which only this module used -/

section

/-! Shared arithmetic and input-buffer invariants of native private-key validation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure PrivateReady (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s

theorem PrivateReady.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : PrivateReady p slots yb xb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

theorem PrivateReady.after_workspace {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ready : ArithmeticReady p.base p.len p.w t) (modulus : numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) : PrivateReady p slots yb xb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Imported private-key validation branches on the scalar validity class disclosed by its status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateMatchCT.lean`, which only this module imported.
section

/-! Computing g^x and comparing it with the imported public value is constant time in x. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem privateMatch_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (fun _ _ => True) := by
  have powers := (powerAt_ct (p := p) (bs := 56) (es := 40) (ec := 44)
    stable h56 h40 h44 h32 p.gLength positive fits count length odd).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.context.gBytes, h.1.scalar⟩,
      ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.context.gBytes, h.2.1.scalar⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPower (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s)
      (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 56 40 44) s (PrivateReady p slots yb xb) := by
    refine WP.mono (powerAt_ok s 56 40 44 h.context stable h56 h40 h44 h32 h.ready h.modulus odd h.r2
      h.context.gBytes p.gLength h.scalar positive fits count) ?_
    rintro u ⟨context, ready, _, modulus, r2, _, frame, rest⟩
    exact ⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (ArithmeticReady p.base p.len p.w) :=
    WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
      (by rw [peerLength]; have := p.minLength; omega) (by rw [peerLength]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [peerLength])) fun _ j => j.2.1
  have equal := equal_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic
  exact relCT_chain powers (fun s h => wpPower s h positive fits count)
    (fun s h => wpPower s h (by rw [← length]; exact positive)
      (by rw [← length]; exact fits) (by rw [← length]; exact count))
    (relCT_chain imports (fun s h => wpImport s h) (fun s h => wpImport s h) (equal.seq finishFlag_ct))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateTailCT.lean`, which only this module imported.
section

/-! Private-key subgroup branches depend on the public value, followed by constant-time consistency checking. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure PrivateMember (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then 1 else 0

theorem PrivateMember.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateMember p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateMember p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateTail_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => PrivateReady p slots yb xb s ∧ s.z = !p.hasQ
  have tests := qTest_ct.mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wpTest (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.qTest s (Q xb) := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have matchCT := privateMatch_ct stable h32 h36 h40 h44 h56 peerLength positive fits count length odd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36)
        (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0)))
        VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic) (fun _ _ => True) := by
    apply iteKnownPair_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
      (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      have subgroup := (subgroup_ct stable h36 h60 h32 hasQ peerLength odd).mono
        (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
        (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.value⟩,
          ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.value⟩, h.2.2⟩) (fun _ _ h => h)
      have wpSubgroup (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
          WP isa (VG.Impl.Ffdh.Arm.Domain.subgroup 36) s (PrivateMember p slots yb xb) := by
        refine WP.mono (subgroup_ok s 36 h.context stable h36 h60 h32 hasQ h.ready h.modulus odd h.r2 h.value peerLength) ?_
        rintro u ⟨context, ready, flag, modulus, r2, frame, rest⟩
        exact ⟨⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, flag⟩
      have matched : RelCT isa (fun s t => PrivateMember p slots yb xb1 s ∧ PrivateMember p slots yb xb2 t ∧ s.sp = t.sp)
          (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (VG.Impl.Ffdh.Arm.Domain.ret 0))
          (fun _ _ => True) := by
        apply ifFlag_pair_ct (decide (Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1))
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
        · intro _
          exact matchCT.mono (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
        · intro _
          exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
      exact (relCT_chain subgroup (fun s h => wpSubgroup s h) (fun s h => wpSubgroup s h) matched).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact matchCT.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests (fun s h => wpTest s h) (fun s h => wpTest s h) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivatePublicCT.lean`, which only this module imported.
section

/-! The public half of private-key checking reveals no private scalar data. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure PrivateImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure PrivateRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem PrivateRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateRanged p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateImport_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true) (h36 : 36 ∈ slots) (h32 : 32 ∈ slots)
    (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (PrivateImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, value⟩

theorem privateRange_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateImported p slots yb xb s) (stable : stableSlots slots = true) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (PrivateRanged p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro u ⟨ready, flag, arrays, frame, rest⟩
  rw [h.imported, h.modulus] at flag
  exact ⟨h.toPrivateReady.after_workspace stable frame rest ready
    ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩

theorem privatePublic_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck (fun _ _ => True) := by
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1) (by decide)).mono
    (P' := fun (s t : State) => PrivateImported p slots yb xb1 s ∧ PrivateImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => PrivateRanged p slots yb xb1 s ∧ PrivateRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (privateTail_ct stable h28 h32 h36 h40 h44 h56 h60 peerLength positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck
  exact relCT_chain imports (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (relCT_chain ranges (fun s h => privateRange_public s h stable odd)
      (fun s h => privateRange_public s h stable odd) branches)

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure PrivateMainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩

structure PrivateScalarImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip xb

structure PrivateScalarRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip xb)

theorem PrivateScalarRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateScalarRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateScalarRanged p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privatePrepare_ready (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateMainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (PrivateReady p slots yb xb) := by
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
  refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ prepareAtWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
  exact ⟨context, ready, modulus, r2, h.value.after_frame frame rest (sourceSep h.value h.valueStack),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack)⟩

theorem privateImport_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (positive : 0 < xb.length) (length : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (PrivateScalarImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    positive (Nat.le_trans length p.width.2.2.2.1) count) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, value⟩

theorem privateRange_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateScalarImported p slots yb xb s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (PrivateScalarRanged p slots yb xb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro u ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, flag⟩

theorem privateMain_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p))
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main (fun _ _ => True) := by
  have pStack (s : State) {xb : List Byte} (h : PrivateMainInput p slots yb xb s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
  have prepare := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.context, h.1.context.pBytes, pStack s h.1⟩,
      ⟨h.2.1.context, h.2.1.context.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (k := xb1.length)
    stable h40 h44 count (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable h28 h32 h60 odd).mono
    (P' := fun (s t : State) => PrivateScalarImported p slots yb xb1 s ∧ PrivateScalarImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => PrivateScalarRanged p slots yb xb1 s ∧ PrivateScalarRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck (VG.Impl.Ffdh.Arm.Domain.ret 2))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p))
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq, ← classification] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (privatePublic_ct stable h28 h32 h36 h40 h44 h56 h60 peerLength positive
        (by have := p.maxLength; omega_using [scalarLength, this]) count length odd).mono
        (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main
  exact relCT_chain prepare (fun s h => privatePrepare_ready s h stable h0 h24 h32 large odd)
    (fun s h => privatePrepare_ready s h stable h0 h24 h32 large odd)
    (relCT_chain imports (fun s h => privateImport_scalar s h stable h40 h44 positive scalarLength count)
      (fun s h => privateImport_scalar s h stable h40 h44 (by rw [← length]; exact positive)
        (by rw [← length]; exact scalarLength) (by rw [← length]; exact count))
      (relCT_chain ranges (fun s h => privateRange_scalar s h stable h28 h32 h60 odd)
        (fun s h => privateRange_scalar s h stable h28 h32 h60 odd) branches))

end VG.Proof.Ffdh.Arm

end

end

/-! Imported private-key checking satisfies the shared timing policy, including its status leakage. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateEntryCT.lean`, which only this module imported.
section

/-! The imported-private-key entry has fixed stack access addresses. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem privateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 24).seq (RelCT.block_append ((storeLocal_ct .r1 28).seq (RelCT.block_append ((storeLocal_ct .r2 32).seq (RelCT.block_append ((storeLocal_ct .r3 36).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r0 140 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateBodyCT.lean`, which only this module imported.
section

/-! Imported private-key checking reveals only public inputs and its documented scalar validity class. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem privateBody_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => PrivateMainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => PrivateMainInput p slots yb xb1 s ∧ PrivateMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : PrivateMainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, h.value.after_frame frame rest (sourceSep h.valueStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack),
      by rw [rest.sp]; exact h.valueStack, by rw [rest.sp]; exact h.scalarStack,
      ⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact privateMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp) (by simp)
        peerLength positive scalarLength count length classification facts.2.1 facts.1 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateFnCT.lean`, which only this module imported.
section

/-! The imported-private-key callable reveals only public inputs and its scalar validity class. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem privateFn_ct {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => PrivateFnInput p yb xb1 s ∧ PrivateFnInput p yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, PrivateFnInput p yb xb s ∧ a = entered s
  have entry := privateEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) a
        (PrivateMainInput p [0, 44, 40, 36, 32, 28, 24] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (privateEntry_ok (entered s) input.args input.incoming input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.value.after_frame frame rest (sourceSep input.valueStack),
      input.scalar.after_frame frame rest (sourceSep input.scalarStack),
      by rw [rest.sp]; exact input.valueStack, by rw [rest.sp]; exact input.scalarStack,
      ⟩
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (privateBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      related.1.length related.1.positive related.1.scalarLength related.1.scalarCount length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem private_contract_ct : ConstantTime isa (Spec.Ffdh.checkPrivateContract abi 128).pre
    (Spec.Ffdh.checkPrivateContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := private_data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.checkPrivateContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6, p7, p8⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p0, ← p1, ← p2, ← p3, ← p5, ← p6] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, statusEq⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := private_input t ht (p := p) (yb := yb) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans domain) (p3.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p2]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    have status := (List.cons.inj statusEq).1
    rw [← domEq, ← peerEq] at status
    simp only [State.addr] at domainBytes peerBytes scalarBytes
    simp only [count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes] at status
    have classification := privateScalarClass_same p (Spec.Rsa.os2ip yb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip xb2) status
    exact (privateFn_ct (by rw [xLength, x2Length]) classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm

end

end


/-! Native ARMv7 imported private-key validation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def privateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x21 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x30 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x3000, 8448⟩]

theorem private_sat : ∃ s, (Spec.Ffdh.checkPrivateContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [privateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using privateSat

theorem private_verified : Verified target VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
    (Spec.Ffdh.checkPrivateContract abi 128) :=
  ⟨private_correct, private_contract_ct, private_sat⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The domain-check entry uses fixed stack addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem domainEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) (fun _ _ => True) := by
  have tail : RelCT isa LocalAddress
      (.block [.mov .r0 (.reg .r3), .str .r0 .r12 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  exact RelCT.block_append (stackAddr_ct.seq
    (RelCT.block_append ((storeLocal_ct .r0 24).seq
    (RelCT.block_append ((storeLocal_ct .r1 28).seq
    (RelCT.block_append ((storeLocal_ct .r2 32).seq tail)))))))

end VG.Proof.Ffdh.Arm

end

end

/-! Exact recognition needs only the public domain and read-only table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

theorem recognition_ct {p : Inputs} {slots : List Nat}
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ TableAt (s.syms tableSym) groups s) ∧
      (Context p slots t ∧ TableAt (t.syms tableSym) groups t) ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      code (fun _ _ => True) := by
  let P := fun s t : State => (Context p slots s ∧ TableAt (s.syms tableSym) groups s) ∧
    (Context p slots t ∧ TableAt (t.syms tableSym) groups t) ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym
  let Q := fun s t : State => ∃ table, ScanReady table p.domain p.k p.dom groups s ∧
    ScanReady table p.domain p.k p.dom groups t
  have stage : RelCT isa P (.block entry) Q := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := entry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, ⟨cu,_,mu⟩,ru⟩ := entry_ok s h.1.1 h24 h28 h32
    obtain ⟨_, v', ev, ⟨cv,_,mv⟩,rv⟩ := entry_ok t h.2.1.1 h24 h28 h32
    obtain ⟨_,rfl⟩ := Exec.det e1 eu
    obtain ⟨_,rfl⟩ := Exec.det e2 ev
    have source (a b : State) (context : Context p slots a)
        (mem : b.mem = a.mem) (rest : VG.Proof.X25519.Arm.Rest [.r4,.r6,.r7,.r8,.r9,.r10] a b) :
        Source p.domain p.k p.dom b :=
      ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega_using [this],
        context.domain.fits, by rw [rest.rd,rest.wr]; exact context.domain.readable,
        by rw [mem]; exact context.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
    have tabU := h.1.2.after mu ru
    have tabV := h.2.1.2.after mv rv
    have symbol : s.syms tableSym = t.syms tableSym := h.2.2.2
    rw [← symbol] at tabV cv
    exact ⟨timing.1, s.syms tableSym,
      ⟨source s u h.1.1 mu ru, tabU, cu⟩, ⟨source t v h.2.1.1 mv rv, tabV, cv⟩⟩
  have scanning : RelCT isa Q loop (fun _ _ => True) := by
    apply RelCT.exists_
    intro table
    exact loop_ct (by decide) (by have := p.maxLength; omega_using [this]) (by decide)
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact stage.seq (scanning.seq restore)

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! ### `Ffdh.Arm.DomainFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.DomainEntry`, which this module and modules that import it used -/

section

/-! The imported-domain ABI arguments are retained in native locals. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

structure DomainEntryRegs (p : Inputs) (s : State) : Prop where
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  scratch : s.gpr .r3 = p.base
  stackBase : s.gpr .r12 = s.sp

theorem DomainEntryRegs.after {p : Inputs} {s t : State}
    (h : DomainEntryRegs p s) (rest : Rest [] s t) : DomainEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.domain, (rest.gpr .r1 (by simp)).trans h.domainLength,
    (rest.gpr .r2 (by simp)).trans h.count, (rest.gpr .r3 (by simp)).trans h.scratch,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem domainEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) s fun t =>
      Context p [0, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have regsU : DomainEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans domain, (moved.other .r1 (by decide)).trans domainLength,
      (moved.other .r2 (by decide)).trans count, (moved.other .r3 (by decide)).trans scratch,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_store_arg .r0 24 argsU (by decide) (by decide) (by decide) regsU.domain regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r1 28 argsV (by decide) (by decide) (by decide) regsV.domainLength regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  rw [restV.sp, restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r2 32 argsW (by decide) (by decide) (by decide) regsW.count regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  rw [restW.sp, restV.sp, restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_mov (op2_reg _ _) fun y moved => ?_
  have restY : Rest [.r0] x y := moved.rest (by simp)
  have argsY := argsX.of_mem moved.mem restY
  have baseY : y.gpr .r0 = p.base := moved.gpr.trans regsX.scratch
  have stackY : y.gpr .r12 = y.sp := (moved.other .r12 (by decide)).trans (regsX.stackBase.trans moved.sp.symm)
  refine wp_store_arg .r0 0 argsY (by decide) (by decide) (by decide) baseY stackY fun t argsT frameT restT => WP.block_nil ?_
  refine ⟨⟨argsT, (restT.gpr .r0 (by simp)).trans baseY⟩, ?_⟩
  rw [restY.sp, restX.sp, restW.sp, restV.sp, restU.sp] at frameT
  rw [moved.mem] at frameT
  exact fullX.trans frameT

end VG.Proof.Ffdh.Arm

end

end

/-! The native domain check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure DomainFnInput (p : Inputs) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  scratch : s.gpr .r3 = p.base
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CheckPublicVerified`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.CheckPublicCorrect`, which only this module used -/

section

/-! The native callable public check satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublic_data (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s) :
    ∃ (p : Inputs) (yb : List Byte), stackArg s 1 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ (s.gpr .r2).toNat = p.k ∧ (stackArg s 2).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧ CheckPublicFnInput p yb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, yLen, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 1
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := 0
    output := 0
    entropy := 0
    len := (stackArg s 2).toNat
    k := (s.gpr .r2).toNat
    privateLength := 0
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rcases domainLen with h | h
        · exact h
        · contradiction }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  exact ⟨p, yb, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    checkPublic_input s original (p := p) (yb := yb) rfl rfl rfl rfl rfl rfl rfl⟩

theorem checkPublic_correct (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckPublic.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPublicContract abi 128).post s t := by
  obtain ⟨p, yb, _, domain, value, count, _, domainBytes, valueBytes, input⟩ := checkPublic_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := checkPublicFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have yLen : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    exact pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change Spec.Ffdh.domainValid (s.gpr .r2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) = true → _
  rw [domain, domainBytes, count]
  intro valid
  rw [yLen, count, value]
  change (t.gpr .r0).toNat = if Spec.Ffdh.publicValid
    ⟨Spec.Ffdh.domainOf p.k (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat),
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k)⟩ then 1 else 0
  rw [domainBytes, valueBytes, result, checkedPublicFlag_spec p (Spec.Rsa.os2ip yb) valid]
  split <;> rfl

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CheckPublicContractCT`, which only this module used -/

section

/-! The native public check has the timing policy of the shared FFDH signature. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CheckPublicBodyCT.lean`, which only this module imported.
section

/-! The public-value body has a trace determined by its documented public inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicBody_ct {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (length : yb.length = p.k) :
    RelCT isa (fun s t => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main) (fun _ _ => True) := by
  let Q := fun s : State => PublicMainInput p (60 :: 56 :: slots) yb s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : PublicMainInput p slots yb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    refine ⟨⟨context, h.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.separate), ?_⟩, zero⟩
    rw [rest.sp]; exact h.separate
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckPublic.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (checkPublicMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp) length facts.2.1 facts.1).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head wp wp branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CheckPublicFnCT.lean`, which only this module imported.
section

/-! The complete callable public check reveals only public FFDH inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicFn_ct {p : Inputs} {yb : List Byte} (length : yb.length = p.k) :
    RelCT isa (fun s t => CheckPublicFnInput p yb s ∧ CheckPublicFnInput p yb t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPublic.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, CheckPublicFnInput p yb s ∧ a = entered s
  have entry := checkPublicEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) a
      (PublicMainInput p [0, 36, 32, 28, 24] yb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (checkPublicEntry_ok (entered s) input.args input.incoming
      input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    refine ⟨context, input.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact input.valueStack), ?_⟩
    rw [rest.sp]; exact input.valueStack
  have body := relCT_chain entry wp wp
    (checkPublicBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) length)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem checkPublic_contract_ct : ConstantTime isa (Spec.Ffdh.checkPublicContract abi 128).pre
    (Spec.Ffdh.checkPublicContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckPublic.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, base, domain, value, count, capacity, domainBytes, valueBytes, inputS⟩ := checkPublic_data s hs
  have lengths (a : State) (h : (Spec.Ffdh.checkPublicContract abi 128).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_pub [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [lengths s hs, lengths t ht, ← p0, ← p1, ← p2, ← p3] at byteEq
  obtain ⟨domEq, yEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have inputT := checkPublic_input t ht (p := p) (yb := yb)
    (p5.symm.trans base) (p0.symm.trans domain) (p3.symm.trans value)
    (by rw [← p2]; exact count) (by rw [← p6]; exact capacity) ?_ ?_
  · exact (checkPublicFn_ct inputS.length s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← value, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← yEq, value, count]
    exact valueBytes

end VG.Proof.Ffdh.Arm

end

end


/-! The native ARMv7 public check is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def publicSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else
    if a = 0x8008 then 0x20 else if a = 0x8009 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x3000, 8448⟩]

theorem checkPublic_sat : ∃ s, (Spec.Ffdh.checkPublicContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [publicSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using publicSat

theorem checkPublic_verified : Verified target VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
    (Spec.Ffdh.checkPublicContract abi 128) :=
  ⟨checkPublic_correct, checkPublic_contract_ct, checkPublic_sat⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.VettedValidation.Fn`, which the modules that import this one used -/

section

/-! The recognized-domain checker uses the existing 128-byte AAPCS frame. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Body.lean`, which only this module imported.
section

/-! Exact recognition proves the existing domain-validity predicate. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups recognize)

theorem body_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.body s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.VettedValidation.body, WP.seq_iff]
  refine WP.mono (VettedGroups.code_ok s h h24 h28 h32 table) ?_
  rintro u ⟨context, cap, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (VettedGroups.zero_test u .r11) ?_
  rintro v ⟨⟨zero, memV⟩, restV⟩
  have value : v.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0) := by
    rw [zero, cap]
  by_cases hit : BitVec.ofNat 32 (recognize groups p.k p.dom) ≠ 0
  · refine WP.ite true (by simp only [eval, value, beq_eq_false_iff_ne.mpr hit]; rfl)
      (fun _ => ?_) (fun bad => Bool.noConfusion bad)
    have recognized : recognize groups p.k p.dom ≠ 0 := by
      intro impossible
      exact hit (by rw [impossible]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (by rw [p.domainLength]; split <;> simp) recognized
    refine WP.mono (ret_ok v 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedDomainFlag_spec, valid]
      exact result
    · rw [memT, memV, memU]
      exact Frame.refl _ _
  · have contextV := context.of_mem memV restV ((restV.gpr .r0 (by simp)).trans context.ptr)
    refine WP.ite false (by rw [Classical.not_not] at hit; simp only [eval, value, hit]; rfl)
      (fun bad => Bool.noConfusion bad) (fun _ => ?_)
    refine WP.mono (domainBody_ok v contextV stable h0 h24 h28 h32) ?_
    rintro t ⟨result, frame⟩
    refine ⟨result, ?_⟩
    rw [memV, memU] at frame
    simpa only [bodyWrites, restV.sp, restU.sp] using frame

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

structure Input (p : Inputs) (s : State) : Prop extends DomainFnInput p s where
  table : VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s)
  safe : VettedGroups.TableSafe ((entered s).syms tableSym) groups
    [⟨State.addr (entered s).sp, 72⟩]

theorem entered_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s)
    (safe : VettedGroups.TableSafe (s.syms tableSym) groups [⟨State.addr s.sp, 72⟩]) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      VG.Impl.Ffdh.Arm.VettedValidation.body) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (domainEntry_ok s h domain domainLength count scratch)) ?_
  rintro u ⟨⟨context, frameU⟩, restU⟩ syms
  have tableU := table.after_frame safe frameU restU
  rw [← syms] at tableU
  refine WP.mono (body_ok u context (by decide) (by decide) (by decide)
    (by decide) (by decide) tableU) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact ⟨result, entryFrame.trans frameT⟩

theorem fn_ok (s : State) {p : Inputs} (h : Input p s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedDomainFlag p := by
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedDomainFlag p) h.saved ?_
  refine WP.mono (entered_ok (entered s) h.args h.domain h.domainLength
    h.count h.scratch h.table h.safe) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm.VettedValidation

end

end

/-! ### `Ffdh.Arm.DomainPre`, which the modules that import this one used -/

section

/-! The shared domain signature supplies the complete native frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem domain_input (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s)
    {p : Inputs} (base : s.gpr .r3 = p.base) (domain : s.gpr .r0 = p.domain)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 0).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom) :
    DomainFnInput p s := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, rd, wr, domS, _, stackDom, stackS, _, domFit, sFit, _, _, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [domain, domLen] at rd domS stackDom domFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackS
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets domOctets stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  refine ⟨stackFit, args, domain, ?_, ?_, base, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm

end

end

/-! A verified native FFDH backend, for domain/key validation and exchange. Callers inherit every implementation's feature requirements. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure Backend where
  checkDomain : Prog isa
  checkDomain_verified : Verified target checkDomain (Spec.Ffdh.checkDomainContract (abi.withConsts VG.Impl.Ffdh.Arm.VettedGroups.tableConsts) 128)
  checkPublic : Prog isa
  checkPublic_verified : Verified target checkPublic (Spec.Ffdh.checkPublicContract abi 128)
  checkPrivate : Prog isa
  checkPrivate_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi 128)
  exchange : Prog isa
  exchange_verified : Verified target exchange (Spec.Ffdh.exchangeContract abi 128)
  suffix : String
  features : List String

end VG.Proof.Ffdh.Arm
