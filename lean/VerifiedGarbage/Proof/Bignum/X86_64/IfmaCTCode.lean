import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode

/-!
# `vg_rsa_private_crt_ifma` on x86-64: constant time but for `n`

`CrtIfma.code` is `Crt.code` with `CrtIfma.main` (`ifmaMain_ct`): the head
and the modulus' check are as in `crtCode_ct`, so the function is constant
time (`ifmaCode_constantTime_of`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

variable (M : Mont)

/-- `vg_rsa_private_crt_ifma` leaks the same in runs that agree on the public
data, given that `main`'s parts do. -/
theorem ifmaCode_ct (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hG : GPowCT M sWsQ)
    (hRY : RedcCT M Public.aY) (hRX : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two CCRel) (CrtIfma.code M.mm) fun _ _ => True := by
  unfold CrtIfma.code
  refine RelCT.seq (R := Two CC3) (RelCT.block_append (RelCT.seq (R := Two CC2) ?_ ?_)) ?_
  · rw [crtEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := crtCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
        ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (CrtHeadPost s) := by
      rw [← crtEntry_split]; exact crtHead_ok c
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.1, c₂.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := crtCtx_of hs.1
    have hnb := c.hnb.congrK h.inScr h.keep
    obtain ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := id hs
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, hn, hk]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    have pin : ∀ p t, (CC3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
      exact hpre.rdi
    refine RelCT.seq (two_piece (Ψ := fun (p : CCPub) t => t.gpr .rsi = p.m.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.m.k ∧ t.gpr .rdi = p.m.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.m.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.m.k) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hpre.rdi⟩
  · -- `main`.
    have toM : ∀ p t, CC3 p t ∧ isa.eval .ne t = some false → Stage R0 p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3_pre h
      obtain ⟨_, _, _, _, _, _, hz⟩ := h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        simp only [eval, hz] at he; simpa using he
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
    exact (ifmaMain_ct M hS hC hQ hP hF hG hRY hRX hL hpost).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem ifmaCode_constantTime_of (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hG : GPowCT M sWsQ)
    (hRY : RedcCT M Public.aY) (hRX : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code M.mm) := by
  refine RelCT.constantTime ((ifmaCode_ct M hS hC hQ hP hF hG hRY hRX hL hpost).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ccPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩

end VG.Proof.Bignum.X86_64
