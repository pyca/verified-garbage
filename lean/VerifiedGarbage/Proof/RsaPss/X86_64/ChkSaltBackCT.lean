module
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtBack

import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFixedSaltCT
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Constant-time public dispatch for PSS salt verification. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- Testing the public salt mode preserves the verification state. -/
theorem saltAny_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H))))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt T (JM T.H (X7 T.H)) a t ∧
      isa.eval .e t = some (decide (vw T.H a 35 = 0))) := by
  refine two_post (vtwo (T := T) (H := T.H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- The bound on the requested length is public too. -/
theorem saltLen_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H))))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt T (JM T.H (X7 T.H)) a t ∧
      isa.eval .b t = some (decide ((a.gpr .r8).toNat < vdb T.H.D a))) := by
  refine two_post (vtwo (T := T) (H := T.H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((s.gpr .r8).toNat < vdb T.H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb T.H.D s < 2 ^ 64 by unfold vdb veml; omega)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.rsl, S.vdb]

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

include hH K hdk in
theorem genericSaltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (genericSaltBack T.f T.H)
      (Two (VAt T (JR T.H))) :=
  RelCT.assoc ((cyd_ct hH hc.verify).seq ((copyDb_ct hH hc.verify).seq
    ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
      ((mhash_ct hH K hdk hc.hash1).seq (cmpH_ct hH hc.verify))))))

include hH K hdk in
theorem saltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (saltBack T.f T.H)
      (Two (VAt T (JR T.H))) := by
  have generic := genericSaltBack_ct hH K hdk hc
  have fixed := fixedSaltBack_ct hH K hdk hc
  unfold saltBack
  refine saltAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (saltLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine fixed.mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.rsl, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Chk
