module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisTimingState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Each public tooth round has a fixed schedule independent of arithmetic residues. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem storeBasis_ct : RelCT isa (Two SquaredBasis) storeBasis (fun _ _ =>True) := by
 unfold storeBasis
 refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x0=q.p.B) ?_ ?_)
  (two_taint [.x0] (fun q s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r;exact hs.trans ht.symm) (by taint_decide))
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>EntryReady (q.p,2^q.b) s) [.x0]
    (fun q s t hs ht r hr =>by
     have eq : r= .x0 := by simpa using hr
     subst r;exact hs.basis.good.x0.trans ht.basis.good.x0.symm) (by taint_decide) ?_)
    (two_map (fun q =>(q.p,2^q.b)) (fun _ _ h =>h) (storeEntry_ct 5 (by decide) (by taint_decide)))
   intro q s h
   refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 (2^q.b) ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [h.basis.good.x0,hdr_enc (show sD<32 by decide),header_read h.basis.good q.p.room (show sD<32 by decide),h.index]
   · rintro t ⟨⟨digit,mem⟩,rest⟩
     exact ⟨⟨h.basis.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.basis.good.x0,mem ▸ h.basis.good.hdr⟩,
      mem ▸ h.context,digit⟩
 · intro q s h
   have bound : 2^q.b≤16 :=Nat.pow_le_pow_right (by decide) (by have :=q.bound;omega : q.b≤4)
   exact WP.mono (basisStore_ok h.basis.good h.space h.context h.index (by omega)) (fun _ ⟨good,_,_,_,_⟩ =>good.x0)

theorem precomputeBasis_ct (M : Mont) : RelCT isa (Two BasisReady) (Precompute.basis M.mm) (fun _ _ =>True) := by
 unfold Precompute.basis
 refine RelCT.seq (two_post (Ψ:=SquaredBasis)
  (two_map basisSquarePublic (fun q s h =>⟨_,h.basis,h.rows⟩) (precomputeSquares_ct M))
  (fun _ _ h =>basisSquared_ok M h)) ?_
 apply RelCT.assoc
 apply RelCT.assoc
 change RelCT isa (Two SquaredBasis) (.seq storeBasis
  (.seq (.loop (Precompute.product M.mm) (.nonzero .x .x3)) (.block Precompute.basisNext))) _
 refine RelCT.seq (two_post (Ψ:=fun q s =>ProductState q.p q.b 1 s) storeBasis_ct (fun _ _ h =>basisStored_ok h)) ?_
 refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x0=q.p.B)
  (two_map (fun q =>(⟨q.p,q.b,q.positive,q.bound⟩ : ProductsPublic)) (fun _ _ h =>h) (precomputeProducts_ct M)) ?_)
  (two_taint [.x0] (fun q s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r;exact hs.trans ht.symm) (by taint_decide))
 intro q s h
 exact WP.mono (precomputeProducts_ok M h q.positive) (fun _ ⟨state,_,_⟩ =>state.basis.good.x0)

end VG.Proof.Ffdh.AArch64.Cached
