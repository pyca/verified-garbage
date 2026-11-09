module

public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
public import VerifiedGarbage.Impl.RsaPss.X86.Table
meta import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
meta import VerifiedGarbage.Impl.RsaPss.X86.Table
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr

/-!
# RSASSA-PSS on x86: a call through the table in the slot `sTab`

`tcallP_vp`: the call of a table's function `k` (`Impl.RsaOaep.X86.tcall`),
from a stage whose slot `sTab` holds the table's address `p`, in a buffer
only read, is a piece (`VP`) as the call of the function `n` it reaches is,
when in every run the table's word `k` and `n`'s address are `a` and an
indirect call of `ts` to `a` reaches `n`. It serves the tables of `MdHash`
as `Proof.RsaOaep.X86.tcallK_vp` serves MGF1's.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (tcall sTab)
open VG.Impl.RsaPss.X86 (ld frameBytes)
open VG.Proof.RsaOaep.X86 (tcall_vp St_roW tload_taint)

theorem twordP_taint {k : Nat} (hk : k < 5) :
    TaintOk [.esp, .ebp, .esi] (.block [.mov .esi (.mem (Impl.RsaPkcs1Sig.X86.at_ .esi (4 * k)))]) := by
  rcases k with _ | _ | _ | _ | _ | k
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · omega

variable {L : Lay} {scr : BitVec 32}

/-- The call of the table's function `k`, among `ts`, in a frame pushing
`rs`, from a stage `F` that an update of `esi` keeps, with `Ctx`, the
statics' addresses of its run, and the table's address `p` in `sTab`. -/
theorem tcallP_vp (hg : Geo L scr) {F G : State → State → Prop} {k : Nat} (hk : k < 5)
    {ts : List (String × Prog isa)} {rs : List Reg} {n : String} {cn : Prog isa} {p a : BitVec 32}
    (hne : ts ≠ []) (hC : ∀ σ s, F σ s → Ctx L scr σ s)
    (hX : ∀ σ s t v, F σ s → Upd s t .esi v → F σ t) (hsy : ∀ σ s, F σ s → s.syms = σ.syms)
    (hT : ∀ σ s, F σ s → s.mem.readW (L.fr sTab) 32 = p)
    (tbl : ∃ R ∈ L.ro, R.Contains (VG.X86.addr p (4 * k)) 4)
    (ha : ∀ σ s, F σ s → σ.mem.readW (VG.X86.addr p (4 * k)) 32 = a ∧ σ.syms n = a ∧
      ts.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms n).setWidth 64) = some (n, cn))
    (h : VP F (.frame (.push rs) (.call n cn) (.pop .eax rs.length)) G) : VP F (tcall k ts rs) G := by
  obtain ⟨tR, tRo, tC⟩ := tbl
  refine tcall_vp (F₁ := fun σ s => F σ s ∧ s.gpr .esi = a) hne ?_ ?_ ?_ (h.mono (fun σ s hs => hs.1) fun _ _ h => h)
  · show VP F (.block ([ld .esi sTab] ++ [.mov .esi (.mem (Impl.RsaPkcs1Sig.X86.at_ .esi (4 * k)))]))
      (fun σ s => F σ s ∧ s.gpr .esi = a)
    refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .esi = p)
      (VP.taint [.esp, .ebp] tload_taint (sp_bp hC) fun σ s hs => ?_)
      (VP.taint [.esp, .ebp, .esi] (twordP_taint hk) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    · simp only [ld, Impl.RsaPkcs1Sig.X86.stk]
      refine (hC σ s hs).wp_slot hg (by decide) (by decide) (by decide) fun t1 _ u1 =>
        WP.block_nil ⟨hX σ s t1 _ hs u1, ?_⟩
      rw [u1.gpr, hT σ s hs]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [(hC _ _ h₁.1).st.sp, (hC _ _ h₂.1).st.sp]
      · rw [(hC _ _ h₁.1).ebp, (hC _ _ h₂.1).ebp]
      · rw [h₁.2, h₂.2]
    · obtain ⟨hF, hsi⟩ := hs
      have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr p (4 * k)) 4 := ⟨tR, (hC σ s hF).st.inRo tRo, tC⟩
      refine wp_ldm (B := p) hsi hin fun t2 u2 => WP.block_nil ⟨hX σ s t2 _ hF u2, ?_⟩
      rw [u2.gpr, St_roW (hC σ s hF).st tRo tC, (ha σ s hF).1]
  · intro σ s ⟨hF, hsi⟩
    obtain ⟨-, hn, hf⟩ := ha σ s hF
    show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .esi).setWidth 64) = some (n, cn)
    rw [hsi, hsy σ s hF, ← hn]
    exact hf
  · intro σ₁ σ₂ s₁ s₂ h₁ h₂
    exact ⟨h₁.2.trans h₂.2.symm, (hC _ _ h₁.1).st.sp.trans (hC _ _ h₂.1).st.sp.symm⟩

end VG.Proof.RsaPss.X86
