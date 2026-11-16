module

public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.PublicDomain
public import VerifiedGarbage.Proof.Dsa.X86.SignLayout
import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
import VerifiedGarbage.Proof.Dsa.X86.SignSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.VerifyLayout
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.SharedPublic
import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.Sized
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SignCompute
import VerifiedGarbage.Proof.Dsa.X86.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.SigningABI
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.WidthDispatch
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! ### `Dsa.X86.SharedTiming`, which only this module used -/

section

/-! ### `Dsa.X86.SigningOperationTiming`, which only this module used -/

section

/-! # Whole signing traces from common public arguments and domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingOperation_agrees {s t : State} (A : SigningABI s) (B : SigningABI t)
    (args : ∀ i < 11, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (signKey s).params.p = (signKey t).params.p)
    (Q : (signKey s).params.q = (signKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Entry.operation true) s tr sf) (F : Exec isa (Entry.operation true) t ur tf) : tr = ur := by
  let L := signLayout s A
  obtain LayoutEq := signLayout_eq A B args SP P Q
  obtain Size := args 10 (by decide)
  obtain Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 9 (by decide))
  obtain PL := args 4 (by decide)
  obtain QL := args 6 (by decide)
  obtain DL := args 8 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s u ∧
    Installed (argumentPointer t 9) ((arg t 10).toNat * 8) Entry.signArguments 2 4 6 t v
  obtain Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, signLayout, Base, Size] using H.2.scr
  obtain hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (4, .pLen) (by decide))
  obtain hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (6, .qLen) (by decide))
  obtain Sized : RelCT isa R (Entry.sized true L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (signSized_relCT L (arg s 8).toNat (arg s 0) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (signInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨⟨signingInstalled_ready A H.1, ?_⟩, signingInstalled_output A H.1, ?_⟩
    · simpa only [L, LayoutEq, DL] using signingInstalled_ready B H.2
    · simpa only [L, LayoutEq, args 0 (by decide)] using signingInstalled_output B H.2
  obtain Dispatch := widthDispatch_relCT true [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  obtain Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 9 Entry.signArguments _ _ _ _ _ _
        ⟨SP, args 9 (by decide), (A.stackArgument (by decide : 9 < 11)).readSrc,
          (B.stackArgument (by decide : 9 < 11)).readSrc⟩ E1 F1
      obtain I := wp_result (signingEntry_ok A) E1
      obtain J := wp_result (signingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          obtain T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.VerifyingOperationTiming`, which only this module used -/

section

/-! # Whole verification traces from common public arguments and domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem verifyingOperation_agrees {s t : State} (A : VerifyingABI s) (B : VerifyingABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (verifyKey s).params.p = (verifyKey t).params.p)
    (Q : (verifyKey s).params.q = (verifyKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Entry.operation false) s tr sf) (F : Exec isa (Entry.operation false) t ur tf) : tr = ur := by
  let L := verifyLayout s A
  obtain LayoutEq := verifyLayout_eq A B args SP P Q
  obtain Size := args 9 (by decide)
  obtain Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 8 (by decide))
  obtain PL := args 2 (by decide)
  obtain QL := args 3 (by decide)
  obtain DL := args 7 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s u ∧
    Installed (argumentPointer t 8) ((arg t 9).toNat * 8) Entry.verifyArguments 0 2 3 t v
  obtain Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, verifyLayout, Base, Size] using H.2.scr
  obtain hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  obtain hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  obtain Sized : RelCT isa R (Entry.sized false L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (verifySized_relCT L (arg s 7).toNat (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (verifyInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨verifyingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using verifyingInstalled_ready B H.2
  obtain Dispatch := widthDispatch_relCT false [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  obtain Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 8 Entry.verifyArguments _ _ _ _ _ _
        ⟨SP, args 8 (by decide), (A.stackArgument (by decide : 8 < 10)).readSrc,
          (B.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1
      obtain I := wp_result (verifyingEntry_ok A) E1
      obtain J := wp_result (verifyingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          obtain T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86

end

end


/-! # Whole-operation constant time against the shared DSA contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem verifyingConstantTime : ConstantTime isa (Spec.Dsa.verifyContract abi 108).pre
    (Spec.Dsa.verifyContract abi 108).pub (Entry.operation false) := by
  intro s t tr ur sf tf S T H E F
  obtain Args := verifyingPublicArgs H
  obtain Domain := verifyingPublicDomain H
  exact verifyingOperation_agrees (verifyingABI_of S) (verifyingABI_of T) Args.2 Args.1 Domain.1 Domain.2 E F

theorem signingConstantTime : ConstantTime isa (Spec.Dsa.signContract abi 108).pre
    (Spec.Dsa.signContract abi 108).pub (Entry.operation true) := by
  intro s t tr ur sf tf S T H E F
  obtain Args := signingPublicArgs H
  obtain Domain := signingPublicDomain H
  exact signingOperation_agrees (signingABI_of S) (signingABI_of T) Args.2 Args.1 Domain.1 Domain.2 E F

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.SignSized`, which only this module used -/

section

/-! ### `Dsa.X86.SignBodySpec`, which only this module used -/

section

/-! ### `Dsa.X86.SignBody`, which only this module used -/

section

/-! # Functional correctness of the post-shape signing body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signBody_ok {base : Addr} {size pLen qLen p q g y x k digestLen digest : Nat} {s0 : State} {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    let accepted := publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
      g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0
    WP isa (SignVerify.signBody pLen qLen) s0 fun sf =>
      sf.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen rv else List.replicate qLen 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64 + BitVec.ofNat 64 qLen) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen sv else List.replicate qLen 0) ∧
      Keeps powerClob s0 sf ∧
      StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  dsimp only
  let accepted := publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
    g ^ x % p = y ∧ g ^ k % p % q ≠ 0 ∧
      k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ≠ 0
  unfold SignVerify.signBody
  refine WP.seq (WP.mono (signCompute_ok M G Y X K D hd hP hg hy hx hk hD)
    fun s1 ⟨M1, R1, S1, F1, E1⟩ => ?_)
  obtain mask1 : flagW base (Layout.field .mask) s1 = mask32 accepted := by
    simpa only [hm, BitVec.allOnes_and] using F1
  obtain ptr1 : pointerValue base s1 (.input .out) = out := by
    rw [runFrame_pointer E1.mem E1.keeps (by decide) (by decide), hp]
  refine wp_seq_assoc (WP.seq (WP.mono (writeSignature_ok M1 (decide accepted)
    (by simpa only [mask32, decide_eq_true_eq] using mask1) R1 S1 ptr1 hf
    (by intro e k h; rw [E1.keeps.2.2]; exact hw e k h) ha)
    fun s2 ⟨R2, S2, F2, K2, O2⟩ => ?_))
  refine WP.mono (result_ok (M1.scr.of_keeps K2 (by decide)) M1.saved accepted (F2.trans mask1))
    fun sf ⟨Vf, Kf, Of⟩ => ?_
  refine ⟨Vf, ?_, ?_, (E1.keeps.trans (K2.mono (by decide))).trans (Kf.mono (by decide)), ?_, ?_⟩
  · simpa only [Of, decide_eq_true_eq] using R2
  · simpa only [Of, decide_eq_true_eq] using S2

  · intro a ha hb hstack
    rw [Of, O2 a (by have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega_using [this] : (qLen + 7) / 8 ≤ 48); change 15712 ≤ ofs base a at ha; omega_using [C, ha]) hb]
    apply E1.mem a ?_ (.inr hstack)
    intro pair hp
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      change 15712 ≤ ofs base a at ha <;> right <;> change _ ≤ ofs base a <;>
      simp only [VG.Impl.Mont.X86.Dynamic.contextBytes, VG.Impl.Mont.X86.Dynamic.slot,
        VG.Impl.Mont.X86.Dynamic.stride, Layout.field, r, usedBytes] <;> omega_using [ha]

  · intro regs saved
    rw [Of]
    exact O2.saved ha
      (by have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega_using [this] : (qLen + 7) / 8 ≤ 48); omega_using [C])
      (by have H : 15712 ≤ size := M.extent; omega_using [H])
      (by have := M.scr.nowrap; omega_using [this]) (E1.saved saved)

end VG.Proof.Dsa.X86

end

end


/-! # The post-shape signing body satisfies the packed-byte signing result -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signBody_spec {base : Addr} {size pLen qLen p q g y x k digestLen n : Nat} {s0 : State} {out : BitVec 32} {key nonce digest : List Byte}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = Spec.Dsa.decodeBE (digest.take n))
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) (qBits : Spec.Dsa.bitLength q = 8 * n) :
    WP isa (SignVerify.signBody pLen qLen) s0 fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s0 sf ∧ StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  obtain spec := signBytes_compute M.widths shape keyLen nonceLen keyValue nonceValue qBits (digest := digest)
  refine WP.mono (signBody_ok M G Y X K D hd hP hg hy hx hk hD hm hp hf hw ha)
    fun sf ⟨V, R, S, Keep, Frame, Saved⟩ => ?_
  obtain B := signatureBytes _ R S
  refine ⟨?_, ?_, Keep, Frame, Saved⟩
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at V
      rw [V]
      rfl
    · rename_i H
      rw [ite_eq_right H] at V
      rw [V]
      rfl
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at B
      exact B
    · rename_i H
      rw [ite_eq_right H] at B
      exact B

end VG.Proof.Dsa.X86

end

end

/-! # The complete public-size signer, including invalid-domain output clearing -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signSized_spec {base : Addr} {size pLen qLen p q g y x k total : Nat}
    {s : State} {out : BitVec 32} {key nonce digest : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (X : CallerBuffer s base size (.input .x) qLen)
    (N : CallerBuffer s base size (.input .nonce) qLen)
    (D : CallerBuffer s base size (.input .digest) total)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (hx : operandValue s base (.input .x) qLen = x)
    (hk : operandValue s base (.input .nonce) qLen = k)
    (hd : (pointerValue base s (.input .digestLen)).toNat = total)
    (hD : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .digest)).setWidth 64) total = digest)
    (ho : pointerValue base s (.input .out) = out)
    (hc : pointerValue base s (.input .qLen) = BitVec.ofNat 32 qLen)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) :
    WP isa (Entry.sized true pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  obtain bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  obtain sz : 8272 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  obtain L : 20 ≤ qLen ∧ qLen ≤ 32 := by unfold Spec.Dsa.lengthsValid at widths; omega_using [widths]
  apply sized_ok true scr extent widths P Q hp hq
  · intro t invalid K O
    obtain rejected : Spec.Dsa.signBytes pLen qLen key nonce digest = none :=
      signBytes_invalid_shape (by simpa only [keyValue] using invalid)
    refine WP.mono (signFailure_ok (scr.of_keeps K (by decide)) (by change 8256 ≤ size; omega_using [sz])
      (by omega_using [L]) L.2 ((shapeFrame_field O (by decide)).trans ho)
      ((shapeFrame_field O (by decide)).trans hc) hf
      (by intro i hi; rw [K.2.2]; exact hw i 1 (by omega_using [hi]))) fun sf ⟨B, V, Of, Kf⟩ => ?_
    obtain F : OutputFrame base (out.setWidth 64) 0 (2 * qLen) t.mem sf.mem :=
      fun a _ hb => Of a (.inr (by omega_using [hb]))
    refine ⟨by rw [V, rejected]; rfl, by rw [rejected]; exact B,
      (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · intro a hbase hout hstack
      exact (F a (by omega_using []) hout).trans (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega_using [hbase])))
    · intro regs saved
      exact F.saved ha (by decide) sz (by have := scr.nowrap; omega_using [this]) (shapeFrame_saved O saved)
  · intro t valid M Dp mask K O
    dsimp only [ite_true]
    rw [hd] at Dp
    obtain Bw := shape_digest_width valid
    obtain hP : pointerValue base t (.input .digestPrefixLen) =
        BitVec.ofNat 32 (min total (Spec.Dsa.bitLength q / 8)) :=
      BitVec.eq_of_toNat_eq (by rw [Dp, BitVec.toNat_ofNat]; omega_using [hd])
    obtain Dt := D.keep_shape O K (by decide) (by decide)
    obtain Db := D.bytes_keep_shape O K (by decide) (by decide) bound
    obtain digestValue : operandValue t base (.input .digest)
        (min total (Spec.Dsa.bitLength q / 8)) = Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength q / 8)) := by
      unfold operandValue
      rw [bytesAt_prefix, Db, hD]
    refine WP.mono (signBody_spec M
      (G.keep_shape O K (by decide) (by decide))
      (Y.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      (N.keep_shape O K (by decide) (by decide))
      (Dt.prefix (Nat.min_le_left _ _))
      (by have B := shape_digest_width valid; omega_using [Bw]) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy)
      ((X.value_keep_shape O K (by decide) (by decide) bound).trans hx)
      ((N.value_keep_shape O K (by decide) (by decide) bound).trans hk)
      digestValue mask ((shapeFrame_field O (by decide)).trans ho) hf
      (by intro e k he; rw [K.2.2]; exact hw e k he) ha
      valid keyLen nonceLen keyValue nonceValue (shape_digest_width valid).1)
      fun sf ⟨V, B, Kf, F, Saved⟩ => ?_
    refine ⟨V, B, (K.mono (by decide)).trans Kf, ?_, fun regs saved => Saved regs (shapeFrame_saved O saved)⟩
    intro a hbase hout hstack
    exact (F a hbase hout (by rw [K.1 .esp (by decide)]; exact hstack)).trans (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega_using [hbase])))

end VG.Proof.Dsa.X86

end

end

/-! # Complete x86 DSA certificates against the shared contracts -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SigningInstalled.lean`, which only this module imported.
section

/-! # Signing original caller bytes after cdecl argument installation -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingInstalled_spec {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.sized true (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (2 * (arg s 6).toNat) =
        result.getD (List.replicate (2 * (arg s 6).toNat) 0) ∧
      Keeps powerClob t sf ∧
      StackOutputFrame (t.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) usedBytes (2 * (arg s 6).toNat) t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 9)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 9)) regs Entry.savedRegisters := by
  dsimp only
  obtain L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    obtain H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (2, .p) ∈ Entry.signArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Nonce, NonceBytes⟩ := I.input (by decide : (5, .nonce) ∈ Entry.signArguments) A.nonceBound
    (by rw [A.rd, A.wr]; simp) A.nonceScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowNonce.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (7, .digest) ∈ Entry.signArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, KeyValue⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr Xptr
  apply signSized_spec (out := arg s 0) I.scr A.used A.lengths P Q G Y X Nonce D rfl rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (8, .digestLen) (by decide))) DigestBytes
    (I.arguments (0, .out) (by decide))
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using I.arguments (6, .qLen) (by decide))
    (by have := A.outBound; have := A.outLength; omega)
    ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) KeyValue
    (congrArg Spec.Dsa.decodeBE NonceBytes.symm)
  intro e k he
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SigningOperation.lean`, which only this module imported.
section

/-! # Complete functional and cdecl verification of the x86 signer -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingOperation_spec {s : State} (A : SigningABI s) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.operation true) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) ((arg s 10).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  dsimp only
  obtain sz : 8272 ≤ (arg s 10).toNat * 8 := by have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega
  unfold Entry.operation Core.sequence
  dsimp only [List.foldr, ite_true]
  refine WP.seq (WP.mono (signingEntry_ok A) fun t I => ?_)
  refine WP.seq (widthDispatch_ok true _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (4, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (6, .qLen) (by decide))) ?_)
  intro u Ku Ou
  obtain J := I.compare Ku Ou
  refine WP.mono (signingInstalled_spec A J) fun v ⟨Value, Bytes, K, O, Saved⟩ => ?_
  obtain Ov : StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0)
      ((arg s 10).toNat * 8) (arg s 1).toNat s.mem v.mem := by
    intro a hb ho hstack
    have H := A.used
    exact (O a (by omega) (by rw [← A.outLength]; exact ho) (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by omega)))
  obtain Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, ?_, restored_abi R Esp (outputFrame_return Ov A.retScratch A.retOut A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem, A.outLength]; exact Bytes
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SharedCorrect.lean`, which only this module imported.
section

/-! # Whole-operation functional correctness against the shared DSA contracts -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem signingSharedPost {s t : State}
    (V : (t.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)))
    (B : Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
      (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)).getD
          (List.replicate (arg s 1).toNat 0)) :
    (Spec.Dsa.signContract abi 108).post s t := by
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _ ∧ _
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨V, B⟩

theorem signingCorrect (s : State) (h : (Spec.Dsa.signContract abi 108).pre s) :
    ∃ trace t, Exec isa (Entry.operation true) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, B, ABI, _⟩ := signingOperation_spec (signingABI_of h)
  exact ⟨trace, t, E, ABI, signingSharedPost V B⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def signingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 40 else if a = 0x2000d then 32 else if a = 0x20010 then 168 else if a = 0x20011 then 1 else if a = 0x20014 then 128 else if a = 0x20019 then 64 else if a = 0x2001c then 20 else if a = 0x20021 then 80 else if a = 0x20029 then 128 else if a = 0x2002d then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩, ⟨0x20004, 44⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi 108).pre s := by
  obtain a0 : arg signingSatState 0 = 4096 := by decide
  obtain a1 : arg signingSatState 1 = 40 := by decide
  obtain a2 : arg signingSatState 2 = 8192 := by decide
  obtain a3 : arg signingSatState 3 = 424 := by decide
  obtain a4 : arg signingSatState 4 = 128 := by decide
  obtain a5 : arg signingSatState 5 = 16384 := by decide
  obtain a6 : arg signingSatState 6 = 20 := by decide
  obtain a7 : arg signingSatState 7 = 20480 := by decide
  obtain a8 : arg signingSatState 8 = 0 := by decide
  obtain a9 : arg signingSatState 9 = 32768 := by decide
  obtain a10 : arg signingSatState 10 = 2048 := by decide
  obtain e : argAddr signingSatState 0 = 0x20004 := by decide
  have esp : signingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, signingSatState] using signingSatState

theorem signing_verified : Verified target (Entry.operation true) (Spec.Dsa.signContract abi 108) :=
  ⟨signingCorrect, signingConstantTime, signingSatisfiable⟩

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def verifyingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 148 else if a = 0x20009 then 1 else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 64 else if a = 0x20018 then 40 else if a = 0x2001d then 80 else if a = 0x20025 then 128 else if a = 0x20029 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 40⟩]

end VG.Proof.Dsa.X86
