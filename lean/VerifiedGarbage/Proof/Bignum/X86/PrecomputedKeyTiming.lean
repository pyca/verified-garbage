module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedKey
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPair
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Importing a public packed key preserves its shared values across executions -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Proof.Mont.X86.Dynamic

def packedKeyTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esp, .esi], flags := false }

theorem precomputedKeyArg_ok {s : State} {p : BitVec 32}
    (P : readSrc s (.mem (PublicFn.argument 2)) = some p) :
    WP isa (.block [.mov .esi (.mem (PublicFn.argument 2))]) s fun t =>
      t.gpr .esi = p ∧ t.mem = s.mem ∧ Keeps [.esi] s t :=
  wp_movS P fun _ U _ => WP.block_nil ⟨U.gpr, U.mem, U.keeps⟩

theorem precomputedKeyArg_relCT (p : BitVec 32) :
    RelCT isa (fun s t => VG.X86.Taint.Agree argumentTaint s t ∧
      readSrc s (.mem (PublicFn.argument 2)) = some p ∧ readSrc t (.mem (PublicFn.argument 2)) = some p)
      (.block [.mov .esi (.mem (PublicFn.argument 2))]) (VG.X86.Taint.Agree packedKeyTaint) := by
  intro s t tr ur sf tf ⟨A, Ps, Pt⟩ E F
  have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint)
      (.block [.mov .esi (.mem (PublicFn.argument 2))]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) argumentTaint (fun _ _ h => h) (hc := .block [])
    rfl
  obtain ⟨Vs, _, Ks⟩ := wp_result (precomputedKeyArg_ok Ps) E
  obtain ⟨Vt, _, Kt⟩ := wp_result (precomputedKeyArg_ok Pt) F
  refine ⟨(CT _ _ _ _ _ _ A E F).1, agree_regs (rs := [.edi, .esp, .esi]) ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · exact Vs.trans Vt.symm

theorem precomputedImport_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree packedKeyTaint) (PublicContext.precomputedImport n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (PublicContext.precomputedImport n) (PublicContext.precomputedImport 1)
    (VG.Taint.hintOf taint packedKeyTaint (PublicContext.precomputedImport 1)) rfl rfl rfl
  rfl

def PackedPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputedPair base bytes len args s t ∧
    wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) =
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) ∧
    wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) =
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len)

theorem precomputedKey_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PrecomputedPair base bytes len args s t ∧
      Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) =
        Spec.Rsa.wordsAt t.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len))
      (PrecomputedFn.importKey (Spec.Rsa.modulusWords len)) (PackedPair base bytes len args) := by
  intro s t tr ur sf tf ⟨H, Key⟩ E F
  have CT := VG.RelCT.seq (precomputedKeyArg_relCT (args 2)) (precomputedImport_relCT (Spec.Rsa.modulusWords len))
  have Trace := (CT _ _ _ _ _ _ ⟨H.agree, (H.left.stack 2 (by decide)).readSrc,
    (H.right.stack 2 (by decide)).readSrc⟩ E F).1
  obtain ⟨Ns, Rs, Os, Ks⟩ := wp_result (PublicContext.precomputedKey_ok H.left) E
  obtain ⟨Nt, Rt, Ot, Kt⟩ := wp_result (PublicContext.precomputedKey_ok H.right) F
  have sz := H.left.space
  have size := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  refine ⟨Trace, H.keep Ks Kt (by decide) (by decide) (Os.mono (by omega) (by omega))
    (Ot.mono (by omega) (by omega)), ?_, ?_⟩
  · rw [Ns, Nt]
    simpa only [Nat.mul_zero] using wv_of_wordsAt Key (c := 0) (w := Spec.Rsa.modulusWords len) (by omega)
  · rw [Rs, Rt]
    exact wv_of_wordsAt Key (by omega)

end VG.Proof.Bignum.X86
