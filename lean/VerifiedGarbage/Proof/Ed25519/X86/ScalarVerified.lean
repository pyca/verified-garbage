module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarContract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
public import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarContract
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! Merged from `Proof.Ed25519.X86.ScalarMain`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_correct {s : State} (h : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hp, hi, ho⟩ := scalarReduce_pre h
  simp only [scalarReduce, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.mono (loadInput_ok hp hi hu (by decide) (dst := 128) (by decide) (by decide) (by decide))
    fun v ⟨hv, words, _⟩ => ?_
  refine WP.seq (WP.mono (scalarEngine_ok (hv.ctx hp.fit hp.wr hp.stk)) fun w ⟨kw, fw, vw⟩ => ?_)
  have hw := hv.scalarEngine hp.fit kw fw
  refine WP.mono (finishWords_ok hp ho hw (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, vw, Spec.Ed25519.scalarReduce, scalarInput_num v.mem hp.fit]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  apply congrArg (· % Spec.Ed25519.L)
  have ew : num (fun k => wv v.mem (arg s 2) (128 + 4 * k)) 16 =
      num (fun k => wv s.mem (arg s 1) (0 + 4 * k)) 16 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (words k hk)
  rw [ew, ← decode_words s.mem 16 (by have := hi.fit; omega_using [this]), addr_zero]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) : VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  obtain ⟨hp, _, ho⟩ := scalarReduce_pre h
  exact scalarTaint_wf hp ho h.2.1 h.2.2.2.2.1

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by native_taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := (scalarReduce_pre hs).1
  have pt := (scalarReduce_pre ht).1
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct h

end VG.Proof.Ed25519.X86
