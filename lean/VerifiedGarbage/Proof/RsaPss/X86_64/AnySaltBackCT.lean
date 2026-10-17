module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyFixedSaltCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBackCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.AnyFixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBackCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-! Constant-time public dispatch for PSS salt verification. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {k g : Nat}

/-- Testing the public salt mode preserves the verification state. -/
theorem saltAny_ctA : RelCT isa (Two (VAtA G k g (JMA H (X7A H))))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAtA G k g (JMA H (X7A H)) a t ∧
      isa.eval .e t = some (decide (vwA H a 35 = 0))) := by
  refine two_post (vtwoA (G := G) (H := H) [35] [] (fun _ => [])
    (fun a t h => jm_vsA h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vwA]

/-- The bound on the requested length is public too. -/
theorem saltLen_ctA : RelCT isa (Two (VAtA G k g (JMA H (X7A H))))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAtA G k g (JMA H (X7A H)) a t ∧
      isa.eval .b t = some (decide ((stackArg a 2).toNat < vdb H.D a))) := by
  refine two_post (vtwoA (G := G) (H := H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vsA h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((stackArg s 2).toNat < vdb H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vwA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb H.D s < 2 ^ 64 by unfold vdb veml; omega)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.arg2, S.vdb]

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH K in
theorem genericSaltBack_ctA (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAtA lk.G k g (JMA H (X7A H)))) (genericSaltBack H)
      (Two (VAtA lk.G k g (JRA H))) :=
  RelCT.assoc ((cyd_ctA hH lk hc.verify).seq ((copyDb_ctA hH hc.verify).seq
    ((shift_ctA hH hc.verify).seq ((verifyNb_ctA hH hc.verify).seq
      ((mhash_ctA hH K hc.hash1).seq (cmpH_ctA hH hc.verify))))))

include hH K in
theorem saltBack_ctA (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAtA lk.G k g (JMA H (X7A H)))) (saltBack H)
      (Two (VAtA lk.G k g (JRA H))) := by
  have generic := genericSaltBack_ctA (k := k) (g := g) hH K lk hc
  have fixed := fixedSaltBack_ctA (k := k) (g := g) hH K lk hc
  unfold saltBack
  refine saltAny_ctA.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (saltLen_ctA.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine fixed.mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (stackArg a 2).toNat < vdb H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.arg2, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Any
