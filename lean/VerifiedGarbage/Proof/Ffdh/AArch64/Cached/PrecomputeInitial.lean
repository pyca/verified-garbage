module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource

import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StoreEntry
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
/-! Initialize entries zero and one from cached R² and the checked generator. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GeneratorBasis.lean`, which only this module imported.
section

/-! Convert the validated generator into the first canonical Montgomery tooth. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generator_basis (M : Mont) {p : Parameters} {s : State} (h : ModState p s)
 (generator : wv s.mem p.B (slot p.w 1) p.w=p.G) (reduced : p.G<p.P) :
 WP isa (M.mm 5 1 4) s fun t =>
 Basis p 1 t ∧ Arrays p.B p.w [2,3,5] s.mem t.mem ∧ Keep mmRegs s t := by
 have r2Bound : wv s.mem p.B (slot p.w 4) p.w<p.P := by
  rw [h.r2];exact Nat.mod_lt _ (by have := p.modulusPositive;omega)
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width
  (by decide : 5<8) (by decide : 1<8) (by decide : 4<8) (by decide) (by decide)
  (by decide) (by decide) (by decide) h.modulus h.inverse r2Bound) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 have mod := h.after_arrays good frame (by decide) (by decide) (by decide)
 have r2Eq : 2^(128*p.w)=2^(64*p.w)*2^(64*p.w) := by rw [←Nat.pow_add];congr 1;omega
 have target : wv t.mem p.B (slot p.w 5) p.w*2^(64*p.w)%p.P=
  (p.G*2^(64*p.w))*2^(64*p.w)%p.P := by
  rw [generator,h.r2,r2Eq,Nat.mul_mod_mod,←Nat.mul_assoc] at product
  exact product
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime target
 rw [Nat.mod_eq_of_lt bound] at cancel
 refine ⟨⟨mod,bound,?_⟩,frame,rest⟩
 simpa only [VG.Proof.Bignum.powMod_eq,Nat.pow_one,Nat.mod_eq_of_lt reduced] using cancel

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GeneratorLoad.lean`, which only this module imported.
section

/-! Load g, immediately after p in the validated domain encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generatorLoad_ok {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (good : Good s p.B p.Z p.w p.mi) (source : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s)
 (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31)
 (domain : word s.mem p.B (8*sDom)=dom) (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k) :
 WP isa (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.B (slot p.w 1) p.w=p.G ∧
 Arrays p.B p.w [1] s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun u =>u.gpr .x1=dom+BitVec.ofNat 64 p.k ∧
  u.gpr .x2=BitVec.ofNat 64 p.k ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read good p.room (show sDom<32 by decide),header_read good p.room (show sLen<32 by decide),domain,length]
 · rintro u ⟨⟨ptr,count,mem⟩,rest⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩
   have src := source.after_inscr (fun x _ => by rw [mem]) rest
   refine WP.mono (loadArray_ok goodU p.room words positive size (by decide : 1<8) src.source src.length ptr count) ?_
   rintro t ⟨goodT,value,frame,keep⟩
   rw [mem] at frame
   exact ⟨goodT,value.trans source.value,frame,(rest.trans keep).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/StoreLiteral.lean`, which only this module imported.
section

/-! Store initial comb entries at fixed public indices. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem storeLiteral_ok {s : State} {p : Parameters} {a d : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (array : a<8) (inside : d<32) :
 WP isa (.seq (.block [movi .x3 d]) (storeEntry a)) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.ctx (entryOffset p.w d) p.w=wv s.mem p.B (slot p.w a) p.w ∧
 Outside p.ctx (entryOffset p.w d) (8*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 d ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [movi_nat (show d<2^16 by omega)]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (storeEntry_ok goodU p.room (by have := p.positive;omega) p.width array
    (memU ▸ context) indexU (entry_fit p inside)
    (fun i hi => (space.after restU).entry_write inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,unchanged,restT⟩
   rw [memU] at value frame unchanged
   exact ⟨goodT,value,frame,unchanged,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem regroup {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := ⟨WP.assoc',WP.assoc⟩

theorem precomputeInitial_ok (M : Mont) {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (generator : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=dom)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) :
 WP isa (Precompute.initial M.mm) s fun t =>
 Basis p 1 t ∧ ContextSpace p t ∧ word t.mem p.B (8*sCtx)=p.ctx ∧
 word t.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) ∧
 TablePrefix p 2 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.initial
 simp only [seqs]
 rw [regroup,WP.seq_iff]
 refine WP.mono (field_initial_power M field) ?_
 rintro a ⟨powerA,frameA,restA⟩
 have inA := InScr.of_arrays frameA p.room (by simp)
 have sourceA := generator.after_inscr inA restA
 have spaceA := space.after restA
 have ctxA := (arrays_header frameA (by decide)).trans context
 have domA := (arrays_header frameA (by decide)).trans domain
 have lenA := (arrays_header frameA (by decide)).trans length
 have rowsA := (arrays_header frameA (by decide)).trans rows
 rw [regroup,WP.seq_iff]
 refine WP.mono (storeLiteral_ok powerA.good spaceA ctxA (by decide : 6<8) (by decide : 0<32)) ?_
 rintro b ⟨goodB,valueB,frameB,sameB,restB⟩
 have powerB := powerA.after_workspace goodB sameB
 have sourceB := sourceA.after_entry frameB (by decide) restB
 have spaceB := spaceA.after restB
 have ctxB := (workspace_header powerA.good sameB (by decide : sCtx<32)).trans ctxA
 have domB := (workspace_header powerA.good sameB (by decide : sDom<32)).trans domA
 have lenB := (workspace_header powerA.good sameB (by decide : sLen<32)).trans lenA
 have rowsB := (workspace_header powerA.good sameB (by decide : sRows<32)).trans rowsA
 have entryB : wv b.mem p.ctx (entryOffset p.w 0) p.w=entryValue p 0 := by
  unfold entryValue
  rw [valueB,powerA.value,VG.Proof.Rsa.FixedBaseComb.exponent_zero]
 have tableB : TablePrefix p 1 b :=
  TablePrefix.extend (fun j hj => by omega : TablePrefix p 0 a) (by decide) frameB entryB
 rw [regroup,WP.seq_iff]
 refine WP.mono (generatorLoad_ok goodB sourceB words positive size domB lenB) ?_
 rintro c ⟨goodC,generatorC,frameC,restC⟩
 have powerC := powerB.after_arrays goodC frameC (by decide) (by decide) (by decide) (by decide)
 have spaceC := spaceB.after restC
 have tableC := tableB.after_inscr spaceB (by decide) (InScr.of_arrays frameC p.room (by simp))
 have ctxC := (arrays_header frameC (by decide)).trans ctxB
 have rowsC := (arrays_header frameC (by decide)).trans rowsB
 rw [WP.seq_iff]
 refine WP.mono (generator_basis M powerC.toModState generatorC reduced) ?_
 rintro d ⟨basisD,frameD,restD⟩
 have spaceD := spaceC.after restD
 have tableD := tableC.after_inscr spaceC (by decide) (InScr.of_arrays frameD p.room (by simp))
 have ctxD := (arrays_header frameD (by decide)).trans ctxC
 have rowsD := (arrays_header frameD (by decide)).trans rowsC
 refine WP.mono (storeLiteral_ok basisD.good spaceD ctxD (by decide : 5<8) (by decide : 1<32)) ?_
 rintro t ⟨goodT,valueT,frameT,sameT,restT⟩
 have basisT := basisD.after_workspace goodT sameT
 have oneExponent : Spec.Rsa.FixedBaseComb.exponent p.N 1=1 := by
  simpa only [Nat.pow_zero,Nat.zero_mul] using VG.Proof.Rsa.FixedBaseComb.exponent_tooth p.N 0 (by decide)
 have entryT : wv t.mem p.ctx (entryOffset p.w 1) p.w=entryValue p 1 := by
  unfold entryValue
  rw [valueT,basisD.value,oneExponent]
 have tableT := tableD.extend (by decide : 1<32) frameT entryT
 have frames : BuildFrame p s.mem t.mem :=
  ((((BuildFrame.of_inscr inA).trans (BuildFrame.of_entry (by decide : 0<32) frameB)).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameC p.room (by simp)))).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameD p.room (by simp)))).trans
    (BuildFrame.of_entry (by decide : 1<32) frameT)
 exact ⟨basisT,spaceD.after restT,(workspace_header basisD.good sameT (by decide : sCtx<32)).trans ctxD,
  (workspace_header basisD.good sameT (by decide : sRows<32)).trans rowsD,tableT,frames,
  ((((restA.trans restB).trans restC).trans restD).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
