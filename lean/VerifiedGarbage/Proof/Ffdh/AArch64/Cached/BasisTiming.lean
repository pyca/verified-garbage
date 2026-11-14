module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasis
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SquaresTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ProductTiming
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.BasisTimingState`, which only this module used -/

section

/-! Functional phase boundaries for the public table's four tooth rounds. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ProductsTiming.lean`, which only this module imported.
section

/-! The subset loop performs exactly 2^b−1 iterations for its public tooth b. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure ProductsPublic where
 p : Parameters
 b : Nat
 positive : 0<b
 limit : b<5

def ProductsReady (q : ProductsPublic) (i : Nat) (s : State) : Prop := ProductState q.p q.b (i+1) s

theorem precomputeProducts_ct (M : Mont) : RelCT isa (Two fun q s =>ProductsReady q 0 s)
 (.loop (Precompute.product M.mm) (.nonzero .x .x3)) (fun _ _ =>True) := by
 have hct : RelCT isa (Two fun (q : ProductsPublic × Nat) s =>q.2<2^q.1.b-1 ∧ ProductsReady q.1 q.2 s)
  (Precompute.product M.mm) (fun _ _ =>True) :=
  two_map (fun q =>(⟨q.1.p,q.1.b,q.2+1⟩ : ProductPublic))
   (fun q s h =>⟨by change q.2+1<2^q.1.b;omega,h.2⟩) (precomputeProduct_ct M)
 have loop := two_loop (cond:= .nonzero .x .x3) (Φ:=ProductsReady) (Ψ:=fun _ _ =>True) (fun q =>2^q.b-1) hct (by
  intro q i s hi h
  have bound : 2^q.b≤16 := Nat.pow_le_pow_right (by decide) (by have := q.limit;omega_using [this] : q.b≤4)
  have atLeast : (2:Nat)^1≤2^q.b := Nat.pow_le_pow_right (by decide) (by have := q.positive;omega_using [this] : 1≤q.b)
  refine WP.mono (precomputeProduct_ok M h (by omega_using [hi] : i+1<2^q.b)) ?_
  rintro t ⟨state,index,_,_⟩
  refine ⟨?_,fun _ =>state,fun _ =>trivial⟩
  rw [eval_nonzero,index,ne_zero_iff]
  have nonzero : ((BitVec.ofNat 64 (i+1+1)-BitVec.ofNat 64 (2^q.b)).toNat≠0) ↔ i+1<2^q.b-1 := by
   rw [BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hi, bound] : i+1+1<2^64),Nat.mod_eq_of_lt (by omega_using [bound] : 2^q.b<2^64)]
   omega_using [hi, bound]
  by_cases more : i+1<2^q.b-1
  · rw [decide_eq_true (nonzero.mpr more),decide_eq_true more]
  · have last : ¬(BitVec.ofNat 64 (i+1+1)-BitVec.ofNat 64 (2^q.b)).toNat≠0 := fun h =>more (nonzero.mp h)
    rw [decide_eq_false last,decide_eq_false more])
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>by
  have atLeast : (2:Nat)^1≤2^q.b := Nat.pow_le_pow_right (by decide) (by have := q.positive;omega_using [this] : 1≤q.b)
  exact ⟨q,⟨by omega_using [atLeast],hs⟩,⟨by omega_using [atLeast],ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure BasisPublic where
 p : Parameters
 b : Nat
 positive : 0<b
 bound : b<5
 bits : 0<p.N ∧ p.N≤8192

def BasisReady (q : BasisPublic) (s : State) : Prop := BasisState q.p q.b s

structure SquaredBasis (q : BasisPublic) (s : State) : Prop where
 bits : 0<q.p.N ∧ q.p.N≤8192
 basis : Basis q.p (2^(q.b*Spec.Rsa.FixedBaseComb.rows q.p.N)) s
 space : ContextSpace q.p s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 index : word s.mem q.p.B (8*sD)=BitVec.ofNat 64 (2^q.b)
 rows : word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N)
 table : TablePrefix q.p (2^q.b) s

def basisSquarePublic (q : BasisPublic) : SquarePublic :=
 ⟨q.p,Spec.Rsa.FixedBaseComb.rows q.p.N,VG.Proof.Rsa.FixedBaseComb.rows_pos q.bits.1,
  by have :=(VG.Proof.Rsa.FixedBaseComb.rows_small q.bits.2).1;omega_using [this]⟩

theorem basisSquared_ok (M : Mont) {q : BasisPublic} {s : State} (h : BasisReady q s) :
 WP isa (Precompute.squares M.mm) s (SquaredBasis q) := by
 refine WP.mono (precomputeSquares_ok M h.basis h.rows (VG.Proof.Rsa.FixedBaseComb.rows_pos h.bits.1)
  (by have :=(VG.Proof.Rsa.FixedBaseComb.rows_small h.bits.2).1;omega_using [this])) ?_
 rintro t ⟨basis,_,frame,rest⟩
 have exponent : 2^((q.b-1)*Spec.Rsa.FixedBaseComb.rows q.p.N)*2^(Spec.Rsa.FixedBaseComb.rows q.p.N)=
  2^(q.b*Spec.Rsa.FixedBaseComb.rows q.p.N) := by
  rw [←Nat.pow_add]
  congr 1
  calc
   (q.b-1)*Spec.Rsa.FixedBaseComb.rows q.p.N+Spec.Rsa.FixedBaseComb.rows q.p.N=
    (q.b-1+1)*Spec.Rsa.FixedBaseComb.rows q.p.N := by ring
   _=q.b*Spec.Rsa.FixedBaseComb.rows q.p.N := by rw [Nat.sub_add_cancel q.positive]
 rw [exponent] at basis
 have inscr :=InScr.of_frm frame (fun r hr =>Nat.le_trans (basisSquareRanges_le q.p.w r hr) q.p.room)
 exact ⟨h.bits,basis,h.space.after rest,(squareFrame_header frame (by decide) (by decide)).trans h.context,
  (squareFrame_header frame (by decide) (by decide)).trans h.index,(squareFrame_header frame (by decide) (by decide)).trans h.rows,
  h.table.after_inscr h.space (by have :=q.bound;have :=Nat.pow_le_pow_right (n:=2) (by decide) (by omega_using [this] : q.b≤4);omega_using [this]) inscr⟩

def storeBasis : Prog isa := .seq (.seq (.block [ldh .x3 sD]) (storeEntry 5)) (.block [movi .x3 1,sth .x3 sJ])

theorem basisStored_ok {q : BasisPublic} {s : State} (h : SquaredBasis q s) :
 WP isa storeBasis s (ProductState q.p q.b 1) := by
 have toothPositive :=Nat.two_pow_pos q.b
 have tooth : 2^q.b≤16 :=Nat.pow_le_pow_right (by decide) (by have :=q.bound;omega_using [this] : q.b≤4)
 unfold storeBasis
 rw [WP.seq_iff]
 refine WP.mono (basisStore_ok h.basis.good h.space h.context h.index (by omega)) ?_
 rintro t ⟨good,value,frame,same,rest⟩
 have basis :=h.basis.after_workspace good same
 have space :=h.space.after rest
 have header (i : Nat) (hi : i<32) :=workspace_header h.basis.good same hi
 have tableEntry : wv t.mem q.p.ctx (entryOffset q.p.w (2^q.b)) q.p.w=entryValue q.p (2^q.b) := by
  unfold entryValue
  rw [value,h.basis.value,VG.Proof.Rsa.FixedBaseComb.exponent_tooth q.p.N q.b q.bound]
 have table:=h.table.extend (by omega_using [tooth] : 2^q.b<32) frame tableEntry
 refine WP.mono (setControlOne_ok good q.p.room (by decide : 16≤sJ) (by decide : sJ<32)) ?_
 rintro u ⟨goodU,one,frameU,restU⟩
 have inscr : InScr q.p.B q.p.Z t.mem u.mem :=InScr.of_outside frameU
  (by have :=hdr_lt_slot q.p.w 8 (show sJ<32 by decide);have :=q.p.room;omega_arith)
 exact ⟨q.bound,⟨by omega_using [],by omega_using [toothPositive]⟩,basis.after_header goodU frameU (by decide),space.after restU,
  (header_other frameU (by decide) (by decide) (by decide)).trans ((header sCtx (by decide)).trans h.context),
  (header_other frameU (by decide) (by decide) (by decide)).trans ((header sD (by decide)).trans h.index),one,
  table.after_inscr space (by omega) inscr,
  (header_other frameU (by decide) (by decide) (by decide)).trans ((header sRows (by decide)).trans h.rows)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
   have bound : 2^q.b≤16 :=Nat.pow_le_pow_right (by decide) (by have :=q.bound;omega_using [this] : q.b≤4)
   exact WP.mono (basisStore_ok h.basis.good h.space h.context h.index (by omega_using [bound])) (fun _ ⟨good,_,_,_,_⟩ =>good.x0)

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
