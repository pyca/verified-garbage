import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Public digit reads recover the loaded byte and agree on the zero branch. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem nafDigitBranch_relCT {K : WinCfg} {base : Addr} {size m j : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {Core : State → Prop}
    {b : BitVec 8} {nonzero : Prog isa} (hb : K.bits+j<size)
    (hc : RegCT [.rdi,.rbx] (.block (Naf.digitRead K)))
    (hbyte : ∀ s,Core s → s.mem (off base (K.bits+j))=b)
    (hkeep : ∀ s t,Keeps [.r8] s t → t.syms=s.syms → Core s → Core t)
    (hn : b≠0 → RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      Core s ∧ Core t ∧ s.gpr .r8=b.setWidth 64 ∧ t.gpr .r8=b.setWidth 64) nonzero
      (fun s t => ∃ E',FieldPair K.M base size m Sl V E' s t)) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      Core s ∧ Core t ∧ s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (.seq (.block (Naf.digitRead K)) (.ite .e (.block []) nonzero))
      (fun s t => ∃ E',FieldPair K.M base size m Sl V E' s t) := by
  have read := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=m)
    (Sl:=Sl) (V:=V) (E:=E) (Pre:=fun s => Core s ∧ s.gpr .rbx=BitVec.ofNat 64 j)
    (Post:=fun s => Core s ∧ s.gpr .r8=b.setWidth 64 ∧ s.zf=some (decide (b=0)))
    (ws:=[.r8]) (by decide) hc
    (fun s t hp ps pt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.1.scr.rdi.trans hp.2.scr.rdi.symm
      · exact ps.2.trans pt.2.symm))
    (fun s hs ps => WP.mono_syms (nafRead_ok hs.scr hb ps.2 (hbyte s ps.1))
      (fun t ⟨tb,tz,kt⟩ st => ⟨⟨hkeep s t kt st ps.1,tb,tz⟩,kt⟩))
  apply RelCT.seq (read.mono (fun _ _ ⟨hp,cs,ct,bs,bt⟩ => ⟨hp,⟨cs,bs⟩,ct,bt⟩) (fun _ _ h => h))
  apply RelCT.ite
  · intro s t ⟨_,cs,ct⟩
    exact cs.2.2.trans ct.2.2.symm
  · exact RelCT.block_nil (fun _ _ h => ⟨E,h.1.1⟩)
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct⟩,he⟩ es et
    have hz : b≠0 := of_decide_eq_false (Option.some.inj (cs.2.2.symm.trans he))
    exact hn hz _ _ _ _ _ _ ⟨hp,cs.1,ct.1,cs.2.1,ct.2.1⟩ es et

end VG.Proof.Weierstrass.X86_64
