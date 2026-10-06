import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure CtLayout where
  B : Addr
  Z : Nat
  w : Nat
  I : Nat
  e : Nat
  hZ : slot w 8≤Z
  hi : I+8≤w
  he : e+64≤Z

def HeadState (L : CtLayout) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I

def Stage (n : Nat) (rs : List Reg) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ s.gpr .rbp=off L.B L.e ∧ value s rs<2^(64*n)

theorem head_pins : Pins HeadState [.rdi] := by
  rintro L s t ⟨mi,hs,_⟩ ⟨mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

def Stores (i : Nat) (lo hi : Reg) : Prog isa :=
  .seq (.block [.store (AdxRotate8.at_ .rsi (16+8*(2*i+1))) lo])
    (.block [.store (AdxRotate8.at_ .rsi (16+8*(2*i+2))) hi])

theorem storeHead_ct (i : Nat) (lo hi : Reg)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rsi]) (Stores i lo hi) hint).isSome=true) :
    RelCT isa (Two HeadState) (AdxTri8.storeHead i lo hi) (fun _ _ => True) := by
  unfold AdxTri8.storeHead
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .rsi=off L.B (slot L.w aAcc+16*L.I))
    [.rdi] head_pins (by taint_decide) ?_) (two_taint [.rsi] ?_ hT)
  · rintro L s ⟨mi,hg,hI⟩
    exact WP.mono (headBases_ok hg.scr hg.rdi hg.hdr L.hZ hI) fun _ h => h.1
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

theorem rowCore_head {i n : Nat} {rs : List Reg} (hr : Regs rs) (hlen : rs.length=n+1)
    (hi : i+n+1≤8) (L : CtLayout) (s : State) (h : Stage n rs L s) :
    WP isa (.block (AdxTri8.rowCore i rs)) s (HeadState L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp,hv⟩ := h
  have he := L.he
  refine WP.mono (rowCore_ok rs hg.scr hp (by rw [hlen]; omega) (by intro eq; rw [eq] at hlen; simp at hlen)
    hr.1 (fun r h => let q := hr.2 r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩)
    (by rw [hlen,Nat.add_sub_cancel]; exact hv)) fun t ⟨_,kt⟩ => ?_
  have dr : t.gpr .rdi=s.gpr .rdi := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,fun h => (hr.2 .rdi h).2.2.2.2 rfl⟩)
  exact ⟨mi,⟨hg.scr.congr kt.2.2.2,dr.trans hg.rdi,kt.2.1 ▸ hg.hdr⟩,kt.2.1 ▸ hI⟩

theorem rowStep_ct {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    {hint htail hmov : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rsi]) (Stores i lo hi) htail).isSome=true)
    (hM : (taint.check (Taint.ofRegs []) (.block [.mov32 lo (.imm 0)]) hmov).isSome=true)
    (hC : (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i (lo::hi::tail))) hint).isSome=true) :
    RelCT isa (Two (Stage (n+1) (lo::hi::tail))) (AdxTri8.rowStep i lo hi tail) (fun _ _ => True) := by
  unfold AdxTri8.rowStep
  refine RelCT.seq (two_piece [.rbp] ?_ hC (rowCore_head hr hlen hi8)) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.2.1.trans ht.2.1.symm
  refine RelCT.seq (storeHead_ct i lo hi hT) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) hM

end VG.Proof.Bignum.X86_64.AdxTri8
