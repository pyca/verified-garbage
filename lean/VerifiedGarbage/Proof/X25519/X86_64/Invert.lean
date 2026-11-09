module

public import VerifiedGarbage.Proof.X25519.Field64Contract
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec
public import VerifiedGarbage.Proof.X25519.X86_64.Env
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
meta import VerifiedGarbage.Proof.X25519.Invert
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec
meta import VerifiedGarbage.Proof.X25519.X86_64.Env
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# X25519 on x86-64: `vg_gf25519_r64_invert`'s power

`invertFn` keeps the callee-saved registers the divsteps write in
`xmm0`–`xmm5` (`invSaves_ok`, `invRestores_ok`), and leaves in slot 17
(byte 544) slot 4's (byte 128) power `p - 2` (`invertFn_pow`, from
`invertDS_pow`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Proof.X25519.Field64 (valAt zAt invAt InvKeeps)

theorem setXmm_gpr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm' (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

/-- `invSaves`: the callee-saved registers in `xmm0`–`xmm5`. -/
theorem invSaves_ok (s : State) :
    WP isa (.block invSaves) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .rbx ∧ s'.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .rbp ∧
      s'.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r12 ∧ s'.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .r13 ∧
      s'.xmm .xmm4 = (0 : BitVec 64) ++ s.gpr .r14 ∧ s'.xmm .xmm5 = (0 : BitVec 64) ++ s.gpr .r15 := by
  apply WP.of_runBlock
  simp only [invSaves, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left', setXmm_gpr', setXmm_mem', setXmm_rd', setXmm_wr', setXmm_xmm',
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `invRestores`: the callee-saved registers out of `xmm0`–`xmm5`, nothing else changed but
them. -/
theorem invRestores_ok (s : State) :
    WP isa (.block invRestores) s fun s' =>
      s'.gpr .rbx = (s.xmm .xmm0).extractLsb' 0 64 ∧ s'.gpr .rbp = (s.xmm .xmm1).extractLsb' 0 64 ∧
      s'.gpr .r12 = (s.xmm .xmm2).extractLsb' 0 64 ∧ s'.gpr .r13 = (s.xmm .xmm3).extractLsb' 0 64 ∧
      s'.gpr .r14 = (s.xmm .xmm4).extractLsb' 0 64 ∧ s'.gpr .r15 = (s.xmm .xmm5).extractLsb' 0 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [invRestores, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setReg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, rfl, rfl, rfl⟩
  all_goals try (simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; done)
  simp only [RegUpd.gpr_setReg_of_ne _ _ a, RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ c,
    RegUpd.gpr_setReg_of_ne _ _ d, RegUpd.gpr_setReg_of_ne _ _ e, RegUpd.gpr_setReg_of_ne _ _ f]

/-- `invertFn` as the inline inversion `invertDS` is to its caller: slot 17
becomes slot 4's power `p - 2`, and only the working area `[512, 768)` and the
registers `clob` and `rbx` change (it keeps more). -/
theorem invertFn_pow [DivstepInv] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa invertFn s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧
      E t.mem base 17 = Spec.X25519.pow (E s.mem base 4) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invSaves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (invertDS_pow baseline_ok hs₁) fun s₂ ⟨g₂, rd₂, wr₂, o₂, e₂⟩ => ?_)
  refine WP.mono (invRestores_ok s₂) fun s₃ ⟨_, _, _, _, _, _, k₃, m₃, rd₃, wr₃⟩ => ?_
  refine ⟨fun r hc hb => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], ?_, ?_⟩
  · have hne : ∀ q ∈ [Reg.rbp, .r12, .r13, .r14, .r15], r ≠ q := fun q hq h => hc (by
      subst h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [k₃ r hb (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp))
      (hne _ (by simp)), g₂ r hc hb, g₁]
  · rw [m₃]; rw [← m₁]; exact o₂
  · rw [m₃, e₂, m₁]

end VG.Proof.X25519.X86_64
