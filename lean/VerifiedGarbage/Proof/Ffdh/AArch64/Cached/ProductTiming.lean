module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ProductIOTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeProduct
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! A subset-product round has a public load, Montgomery multiplication, and public store. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ProductPublic where
 p : Parameters
 b : Nat
 j : Nat

def ProductReady (q : ProductPublic) (s : State) : Prop :=
 q.j<2^q.b ∧ ProductState q.p q.b q.j s

def ProductLoaded (q : ProductPublic) (s : State) : Prop :=
 ProductReady q s ∧ wv s.mem q.p.B (slot q.p.w 1) q.p.w=entryValue q.p q.j

def productIO (q : ProductPublic) : ProductIO := ⟨q.p,q.j,2^q.b⟩
def productWs (q : ProductPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem ProductReady.io {q : ProductPublic} {s : State} (h : ProductReady q s) : ProductIOReady (productIO q) s :=
 ⟨h.2.basis.good,h.2.context,h.2.index,h.2.basisIndex⟩

theorem precomputeProduct_ct (M : Mont) : RelCT isa (Two ProductReady) (Precompute.product M.mm) (fun _ _ =>True) := by
 unfold Precompute.product
 refine RelCT.seq (two_post (Ψ:=ProductLoaded)
  (two_map productIO (fun _ _ h =>h.io) productLoad_ct) ?_) ?_
 · intro q s h
   refine WP.mono (productLoad_ok h.2.basis.good h.2.space h.2.context h.2.index (by have := h.2.limit;have := Nat.two_pow_pos q.b;omega)) ?_
   rintro t ⟨good,selected,frame,rest⟩
   have basis := h.2.basis.after_arrays good frame (by decide) (by decide) (by decide) (by decide)
   have state := h.2.after_arrays basis frame rest (by simp)
   exact ⟨⟨h.1,state⟩,selected.trans (h.2.table q.j (by have := h.2.position;have := Nat.two_pow_pos q.b;omega))⟩
 · refine RelCT.seq (two_post (Ψ:=ProductReady)
    (two_map productWs (fun q s h =>⟨q.p.mi,h.1.2.basis.good,q.p.room⟩)
     (M.ct (by simp [MmUse,Public.aY,Public.aX,Public.aXm]))) ?_) ?_
   · intro q s h
     refine WP.mono (basis_product M h.1.2.basis h.2) ?_
     rintro t ⟨_,basis,frame,rest⟩
     exact ⟨h.1.1,h.1.2.after_arrays basis frame rest (by simp)⟩
   · refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x0=q.p.B)
      (two_map productIO (fun _ _ h =>h.io) productStore_ct) ?_)
      (two_taint [.x0] ?_ (by taint_decide))
     · intro q s h
       have destination : q.j+2^q.b<32 := by
        have bound : 2^q.b≤16 := Nat.pow_le_pow_right (by decide) (by have := h.2.tooth;omega : q.b≤4)
        have := h.1
        omega
       refine WP.mono (productStore_ok h.2.basis.good h.2.space h.2.context h.2.index h.2.basisIndex destination) ?_
       rintro t ⟨good,_,_,_,_⟩
       exact good.x0
     · intro q s t hs ht r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.trans ht.symm

end VG.Proof.Ffdh.AArch64.Cached
