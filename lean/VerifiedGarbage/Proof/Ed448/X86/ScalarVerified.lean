module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
public import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAddMain
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAddMain
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
meta import VerifiedGarbage.Proof.Ed448.ScalarWords
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Basic
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.X86.Carry
meta import VerifiedGarbage.Proof.X448.X86.Columns
meta import VerifiedGarbage.Proof.X448.X86.Copy
meta import VerifiedGarbage.Proof.X448.X86.FnVerified
meta import VerifiedGarbage.Proof.X448.X86.Frame
meta import VerifiedGarbage.Proof.X448.X86.Freeze
meta import VerifiedGarbage.Proof.X448.X86.Ops
meta import VerifiedGarbage.Proof.X448.X86.Restore
meta import VerifiedGarbage.Proof.X448.X86.Select
meta import VerifiedGarbage.Proof.X448.X86.Small
meta import VerifiedGarbage.Proof.X448.X86.Step
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 scalar arithmetic on x86 (32-bit): `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: the only branches are on the
loop counters, and every address is a pointer plus a constant or a counter.
The local contracts only read the arguments; the shared contract of `Spec/`
lets the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`). A concrete witness proves it satisfiable.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Impl.Ed448.X86 (scalarReduce scalarMulAdd)

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` (argument `scidx` of `argc`) known to be the base
addresses of the writable regions. -/
def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [57, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {argc scidx : Nat} (hp : Args s argc scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hos : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s scidx)))
    (hofit : (arg s 0).toNat + 57 ≤ 2 ^ 32)
    (hret : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩)
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩) :
    VG.X86.Taint.Wf (scalarTaint scidx argc) s := by
  have hf := hp.sc_fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, scalarTaint], by simpa [hw] using hos, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, hofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 57⟩, scR (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [scalarTaint] at hk
    rw [show VG.X86.Taint.depth (scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))

/-! ## Reduction -/

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := ReducePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := ReducePre.of hs
  have pt := ReducePre.of ht
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct (ReducePre.of h)

/-! ## Multiply-add -/

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  have hp := MulAddPre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := MulAddPre.of hs
  have pt := MulAddPre.of ht
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct (MulAddPre.of h)

end VG.Proof.Ed448.X86
