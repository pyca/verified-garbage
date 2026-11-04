module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
public import VerifiedGarbage.Impl.RsaPss.Arm.Table
public import VerifiedGarbage.Impl.MdHashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
meta import VerifiedGarbage.Impl.RsaPss.Arm.Table
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS on ARMv7: the calls through a table of `MdHash`

`HTab`: what `ctHash` needs of the table of `MdHash` at `p`, in the run from
`σ`: its words 0, 3 and 4 hold the addresses `ai`, `ac` and `ad` (the same in
every run) of the hash function's streaming `init`, compression function and
digest (`dn`), which an indirect call of `f`'s functions to that address
reaches. `htcall_vp`: from a stage whose slot `sTab` holds `p`, the call of
the table's function `k` (`Impl.RsaOaep.Arm.tcall`) is the call of the
function it reaches, as RSAES-OAEP's MGF1 calls the functions of a table of
`Hash` (`Proof/RsaOaep/Arm/Mgf.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (tA wp_ldrT wp_ldS St_roR St_roW tcall_vp)
open VG.Impl.RsaOaep.Arm (tcall tload sTab)

/-- What the code needs of the table of `MdHash` at `p` for the hash
function `h`, whose digest is named `dn`, in the run from `σ`. -/
structure HTab (h : PssHash) (dn : String) (f : MdFns) (p ai ac ad : BitVec 32) (σ : State) : Prop where
  i : f.init.find? (fun q => (σ.syms q.1).setWidth 64 == ai.setWidth 64) = some (h.H.md.st.initN, h.H.md.st.initC)
  c : f.comp.find? (fun q => (σ.syms q.1).setWidth 64 == ac.setWidth 64) = some (h.H.md.compN, h.H.md.compC)
  d : f.dig.find? (fun q => (σ.syms q.1).setWidth 64 == ad.setWidth 64) =
    some (dn, Impl.MdHashTable.Arm.digest h.H.md.out)
  m0 : σ.mem.readW (tA p 0) 32 = ai
  m3 : σ.mem.readW (tA p 12) 32 = ac
  m4 : σ.mem.readW (tA p 16) 32 = ad

/-- The loads of the table's words 0, 3 and 4. -/
theorem hword_cert {k : Nat} (hk : k = 0 ∨ k = 3 ∨ k = 4) :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4]) (.block [.ldr .r4 .r4 (4 * k)]) hc).isSome = true := by
  rcases hk with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

variable {L : Lay} {scr : BitVec 32}

/-- The call of the table's function `k`, among `ts`, from a stage `F` whose
slot `sTab` holds `p`, the table being in a buffer only read: the table's
word `k`, `a` in every run, reaches `(n, c)`. -/
theorem htcall_vp (hg : Geo L scr) {F G : State → State → Prop} {p : BitVec 32}
    (hF : ∀ σ s, F σ s → Ctx L scr σ s ∧ s.syms = σ.syms ∧ s.mem.readW (L.fr sTab) 32 = p)
    (hX : ∀ σ s v, F σ s → F σ (s.setReg .r4 v))
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA p o) 4)
    {k : Nat} (hk : k = 0 ∨ k = 3 ∨ k = 4) {ts : List (String × Prog isa)} (hne : ts ≠ []) {a : BitVec 32}
    {n : String} {c : Prog isa}
    (ha : ∀ σ s, F σ s → σ.mem.readW (tA p (4 * k)) 32 = a ∧
      ts.find? (fun q => (σ.syms q.1).setWidth 64 == a.setWidth 64) = some (n, c))
    (h : VP F (.call n c) G) : VP F (tcall k ts) G := by
  have hk4 : 4 * k + 4 ≤ 44 := by omega
  obtain ⟨tR, tRo, tC⟩ := hR
  refine tcall_vp hne (F₁ := fun σ s => F σ s ∧ s.gpr .r4 = a) ?_ (fun σ s ⟨hs, hr4⟩ => ?_)
    (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (h.mono (fun _ _ hh => hh.1) fun _ _ hh => hh)
  · show VP F (.block ([Impl.RsaPss.Arm.ld .r4 sTab] ++ [.ldr .r4 .r4 (4 * k)])) (fun σ s => F σ s ∧ s.gpr .r4 = a)
    refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .r4 = p)
      (VP.ldrSp (c := [(.r4, sTab)]) (fun _ _ _ _ h₁ h₂ => (hF _ _ h₁).1.st.sp.trans (hF _ _ h₂).1.st.sp.symm)
        fun σ s hs => WP.mono (wp_ldS hg (hF σ s hs).1 (r := .r4) (by decide) (by decide)) fun t e => ?_)
      (VP.taint [.r4] (hword_cert hk) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    · subst e
      exact ⟨hX σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]; exact (hF σ s hs).2.2⟩
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    · obtain ⟨hs', hsi⟩ := hs
      have hc := (hF σ s hs').1
      refine WP.mono (wp_ldrT (by omega) hsi (St_roR hc.st tRo (tC _ hk4))
        ((St_roW hc.st tRo (tC _ hk4)).trans (ha σ s hs').1)) fun t e => ?_
      subst e
      exact ⟨hX σ s _ hs', by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩
  · show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .r4).setWidth 64) = _
    rw [hr4, (hF σ s hs).2.1]; exact (ha σ s hs).2

end VG.Proof.RsaPss.Arm
