module

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.Guarded
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.Guarded
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The code after the check of `e`, with any constant-time `rest`. -/
theorem codeWith_ct (rest : Prog isa) (hrest : RelCT isa (Two DRel) rest fun _ _ => True) :
    RelCT isa (Two CR) (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) fun _ _ => True := by
  refine RelCT.seq (R := Two CE2) ?_ ?_
  · rw [pdEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CE1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := pdCtx_of hs.1
    have hZ := c.hZ
    have hk1 := c.hk1
    have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
        Precomputed.entry.drop 1)) s (PdEnt s) := by
      rw [← pdEntry_split]; exact pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw', h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw'⟩
  refine RelCT.seq (R := Two CL) (two_post (wordPdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => ce2_lh h) h)
    fun _ _ h => h) fun p t h => ce2_wordLoad h) ?_
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, _, _, z₂, _⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .rsi = p.d.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.d.k ∧ t.gpr .rdi = p.d.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(cl_fail h₁.1).2.1, (cl_fail h₂.1).2.1])
      (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK⟩ := cl_fail h
    have hn := hs.nowrap
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.d.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.d.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.d.k) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `rest`.
    exact two_map (fun p => p.d) (fun _ _ h => cl_rest h.1 h.2) hrest

theorem code_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) : RelCT isa (Two CR) (Folded.code M.mm) fun _ _ => True :=
  codeWith_ct (Folded.rest M.mm) (rest_ct M hfinal)

/-- The code after the check of `e` is constant time, for valid `e`s, with any
constant-time `rest`. -/
theorem codeWith_constantTime (rest : Prog isa) (hrest : RelCT isa (Two DRel) rest fun _ _ => True) :
    ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub
      (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code)) (.ite .e fail rest))) := by
  refine RelCT.constantTime ((codeWith_ct rest hrest).mono (fun s₁ s₂ ⟨⟨h₁, v₁⟩, ⟨h₂, _⟩, hp⟩ => ⟨cpubOfD s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, v₁⟩
  · obtain ⟨hr, a0, -, a2, a3, hw, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    have c := pdCtx_of h₂
    have hpl := c.hpl
    rw [r .rcx (by decide), r .rsi (by decide)] at hpl
    rw [r .rdx (by decide), r .rcx (by decide)] at hw
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rsi (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, he.symm, ?_, ?_, v₁⟩
    · rw [r .rdx (by decide), r .rsi (by decide), show (0 : Nat) = 8 * 0 from rfl]
      exact (wv_of_wordsAt hw (by omega)).symm
    · rw [r .rdx (by decide), r .rsi (by decide)]
      exact (wv_of_wordsAt hw (by omega)).symm

/-- The code after the check of `e` is constant time, for valid `e`s. -/
theorem code_constantTime (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub (Folded.code M.mm) :=
  codeWith_constantTime (Folded.rest M.mm) (rest_ct M hfinal)

end VG.Proof.Bignum.X86_64.FoldedPublic
