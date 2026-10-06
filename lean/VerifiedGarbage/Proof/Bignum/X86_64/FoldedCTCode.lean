import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTMain

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem code_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) : RelCT isa (Two CR) (Folded.code M.mm) fun _ _ => True := by
  unfold Folded.code
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
  refine RelCT.seq (R := Two CL) (two_post (pdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => ce2_lh h) h)
    fun _ _ h => h) fun p t h => ce2_load h) ?_
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
    exact two_map (fun p => p.d) (fun _ _ h => cl_rest h.1 h.2) (rest_ct M hfinal)

theorem code_constantTime (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) : ConstantTime isa pdContract.pre pdContract.pub (Folded.code M.mm) := by
  refine RelCT.constantTime ((code_ct M hfinal).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpubOfD s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, -, a2, a3, hw, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    have c := pdCtx_of h₂
    have hpl := c.hpl
    rw [r .rcx (by decide), r .rsi (by decide)] at hpl
    rw [r .rdx (by decide), r .rcx (by decide)] at hw
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rsi (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, he.symm, ?_, ?_⟩
    · rw [r .rdx (by decide), r .rsi (by decide), show (0 : Nat) = 8 * 0 from rfl]
      exact (wv_of_wordsAt hw (by omega)).symm
    · rw [r .rdx (by decide), r .rsi (by decide)]
      exact (wv_of_wordsAt hw (by omega)).symm

end VG.Proof.Bignum.X86_64.FoldedPublic
