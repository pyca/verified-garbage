import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def Pre (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧ X < p.N ∧
    X % p.N = x * 2^(64*p.L.w) % p.N

def Ready (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w % p.N = x * 2^(64*p.L.w) % p.N

theorem start_fw (p : PublicData) (s : State) (h : Pre p s) :
    WP isa Precomputed.start s (Ready p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (start_ok hc hf.1 (by have := hf.2.1; omega) hf.2.2.1)
    fun t ⟨ct,yt,_,_,_⟩ => ⟨X,x,ct,hf,by rw [yt]; exact hlt,by rw [yt]; exact hx⟩

theorem init_fw (p : PublicData) (s : State) (h : Ready p s) :
    WP isa (.block [.mov32 .rax (.imm 16), .store (hdr sI) .rax]) s (Inv p 0) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  have hb : p.L.B.toNat + slot p.L.w 8 ≤ 2^64 := by
    have := hc.good.scr.nowrap; have := hf.1; omega
  refine WP.mono (init_ok hc.good hf.1) fun t ⟨mt,kt⟩ => ?_
  have ct := ExpCtx.store hc hf.1 (i := sI) (by decide) (by decide) mt kt.2.2
    ((kt.gpr (by decide)).trans hc.good.rdi)
  have yt : wv t.mem p.L.B (slot p.L.w aY) p.L.w = wv s.mem p.L.B (slot p.L.w aY) p.L.w := by
    rw [mt,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]
  exact ⟨t,X,x,⟨ct,by rw [yt]; exact hlt,by simpa only [yt,Nat.pow_zero,Nat.pow_one] using hx,
    by rw [mt,word_writeW_self]; rfl,Frm.refl _ _ _,Keep.refl _ _⟩,hf⟩

/-- The caller supplies the final multiplication's leakage proof separately;
this extends no existing Montgomery contract or permitted-use list. -/
theorem exp65537_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two Pre) (Folded.exp65537 M.mm) (fun _ _ => True) := by
  unfold Folded.exp65537
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : PublicData => p.L)
    (fun _ _ ⟨_,_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩) VG.Proof.Bignum.X86_64.start_ct) start_fw) ?_
  refine RelCT.seq (two_piece [.rdi]
    (fun p s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst r; rw [hs.good.rdi,ht.good.rdi])
    (by taint_decide) init_fw) ?_
  refine RelCT.seq (two_map id (fun _ _ h => ⟨by decide,h⟩) (squares_ct M)) ?_
  exact two_map (fun p : PublicData => p.L) (fun _ _ ⟨_,_,_,h,hf⟩ => ⟨h.ctx.good,hf.1⟩) hfinal

end VG.Proof.Bignum.X86_64.FoldedPublic
