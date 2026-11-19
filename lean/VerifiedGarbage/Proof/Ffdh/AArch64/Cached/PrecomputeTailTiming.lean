module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasis
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ConstTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadTiming
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StoreEntry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout

/-! ### `Ffdh.AArch64.Cached.EntryTiming`, which only this module used -/

section

/-! Public entry addressing and fixed-length stores have no residue-dependent trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure EntryReady (q : Parameters × Nat) (s : State) : Prop where
 good : Good s q.1.B q.1.Z q.1.w q.1.mi
 context : word s.mem q.1.B (8*sCtx)=q.1.ctx
 digit : s.gpr .x3=BitVec.ofNat 64 q.2

theorem storeEntryHead_ok {s : State} {p : Parameters} {j a : Nat}
 (h : EntryReady (p,j) s) (array : a<8) :
 WP isa (.block (entryPtr++[ldh .x16 (sArr a)])) s fun t =>
 t.gpr .x16=off p.B (slot p.w a) ∧ t.gpr .x17=off p.ctx (entryOffset p.w j) ∧
 t.gpr .x12=BitVec.ofNat 64 p.w := by
 rw [WP.block_append_iff]
 refine WP.mono (entryPtr_ok h.good p.room h.context h.digit) ?_
 rintro u ⟨⟨pointer,count,mem⟩,rest⟩
 have arrHdr : sArr a<32 := by unfold sArr;omega_using [array]
 have good : Good s p.B p.Z p.w p.mi := h.good
 change u.gpr .x17=off p.ctx (entryOffset p.w j) at pointer
 change u.gpr .x12=BitVec.ofNat 64 p.w at count
 brun [rest.rd,rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
  hdr_enc arrHdr,good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot p.w 8 arrHdr;have := p.room;omega_arith),
  mem,good.hdr.harr a array,pointer,count]

theorem storeEntry_ct (a : Nat) (array : a<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0,.x3]) (.block (entryPtr++[ldh .x16 (sArr a)])) hc).isSome=true) :
 RelCT isa (Two EntryReady) (storeEntry a) (fun _ _ => True) := by
 unfold storeEntry
 refine RelCT.seq (two_piece (Ψ:=fun q s =>
  s.gpr .x16=off q.1.B (slot q.1.w a) ∧ s.gpr .x17=off q.1.ctx (entryOffset q.1.w q.2) ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w) [.x0,.x3] ?_ check (fun _ _ h =>storeEntryHead_ok h array))
  (two_taint [.x16,.x17,.x12] ?_ (by taint_decide))
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.good.x0.trans ht.good.x0.symm
   · exact hs.digit.trans ht.digit.symm
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

theorem loadEntryHead_ok {s : State} {p : Parameters} {j a : Nat}
 (h : EntryReady (p,j) s) (array : a<8) :
 WP isa (.block (entryPtr++[mov .x16 .x17,ldh .x17 (sArr a)])) s fun t =>
 t.gpr .x16=off p.ctx (entryOffset p.w j) ∧ t.gpr .x17=off p.B (slot p.w a) ∧
 t.gpr .x12=BitVec.ofNat 64 p.w := by
 rw [WP.block_append_iff]
 refine WP.mono (entryPtr_ok h.good p.room h.context h.digit) ?_
 rintro u ⟨⟨pointer,count,mem⟩,rest⟩
 have arrHdr : sArr a<32 := by unfold sArr;omega_using [array]
 have good : Good s p.B p.Z p.w p.mi := h.good
 change u.gpr .x17=off p.ctx (entryOffset p.w j) at pointer
 change u.gpr .x12=BitVec.ofNat 64 p.w at count
 brun [rest.rd,rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
  hdr_enc arrHdr,good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot p.w 8 arrHdr;have := p.room;omega_arith),
  mem,good.hdr.harr a array,pointer,count]

theorem loadEntry_ct (a : Nat) (array : a<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0,.x3])
  (.block (entryPtr++[mov .x16 .x17,ldh .x17 (sArr a)])) hc).isSome=true) :
 RelCT isa (Two EntryReady) (loadEntry a) (fun _ _ => True) := by
 unfold loadEntry
 refine RelCT.seq (two_piece (Ψ:=fun q s =>
  s.gpr .x16=off q.1.ctx (entryOffset q.1.w q.2) ∧ s.gpr .x17=off q.1.B (slot q.1.w a) ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w) [.x0,.x3] ?_ check (fun _ _ h =>loadEntryHead_ok h array))
  (two_taint [.x16,.x17,.x12] ?_ (by taint_decide))
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.good.x0.trans ht.good.x0.symm
   · exact hs.digit.trans ht.digit.symm
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.FieldFrame`, which only this module used -/

section

/-! Public-context writes leave the loaded modulus and R² unchanged. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem FieldInitial.after_workspace {p : Parameters} {s t : State} (h : FieldInitial p s)
 (good : Good t p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) : FieldInitial p t := by
 have inverseWord : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) :=
  workspace_word (by have := h.good.scr.nowrap;omega_using [this]) same
   (by have := slot_le (w:=p.w) (by decide : 0<8);have := p.room;have := p.positive;omega_arith)
 refine ⟨good,(workspace_array h.good same (by decide)).trans h.modulus,?_,
  (workspace_array h.good same (by decide)).trans h.r2⟩
 rw [inverseWord]
 exact h.inverse

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeInitial`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.GeneratorSource`, which this module and modules that import it used -/

section

/-! The checked generator's public bytes remain outside both working buffers. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure GeneratorSource (p : Parameters) (ptr : Addr) (bs : List Byte) (s : State) : Prop where
 source : Src s p.B p.Z ptr bs
 length : bs.length=p.k
 value : Spec.Rsa.os2ip bs=p.G
 separate : ∀ i<bs.length,8*(3+34*p.w)≤ofs p.ctx (ptr+BitVec.ofNat 64 i)

theorem GeneratorSource.after_inscr {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : GeneratorSource p ptr bs s) (frame : InScr p.B p.Z s.mem t.mem) (rest : Keep rs s t) : GeneratorSource p ptr bs t :=
 ⟨h.source.congrK frame rest,h.length,h.value,h.separate⟩

theorem GeneratorSource.after_entry {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg} {j : Nat}
 (h : GeneratorSource p ptr bs s) (frame : Outside p.ctx (entryOffset p.w j) (8*p.w) s.mem t.mem)
 (inside : j<32) (rest : Keep rs s t) : GeneratorSource p ptr bs t := by
 refine ⟨⟨?_,?_,h.source.out⟩,h.length,h.value,h.separate⟩
 · intro i hi;rw [rest.rd,rest.wr];exact h.source.rd i hi
 · intro i hi
   rw [frame _ (Or.inr (by have := entry_within p inside;have := h.separate i hi;omega_arith))]
   exact h.source.val i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end

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
 obtain r2Bound : wv s.mem p.B (slot p.w 4) p.w<p.P := by
  rw [h.r2];exact Nat.mod_lt _ (by have := p.modulusPositive;omega_using [reduced])
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width
  (by decide : 5<8) (by decide : 1<8) (by decide : 4<8) (by decide) (by decide)
  (by decide) (by decide) (by decide) h.modulus h.inverse r2Bound) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 obtain mod := h.after_arrays good frame (by decide) (by decide) (by decide)
 obtain r2Eq : 2^(128*p.w)=2^(64*p.w)*2^(64*p.w) := by rw [←Nat.pow_add];congr 1;omega_using []
 obtain target : wv t.mem p.B (slot p.w 5) p.w*2^(64*p.w)%p.P=
  (p.G*2^(64*p.w))*2^(64*p.w)%p.P := by
  rw [generator,h.r2,r2Eq,Nat.mul_mod_mod,←Nat.mul_assoc] at product
  exact product
 obtain cancel := VG.Proof.Bignum.mont_cancel p.coprime target
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
   obtain goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩
   obtain src := source.after_inscr (fun x _ => by rw [mem]) rest
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
 · brun [movi_nat (show d<2^16 by omega_using [inside])]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   obtain goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (storeEntry_ok goodU p.room (by have := p.positive;omega_using [this]) p.width array
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
 obtain inA := InScr.of_arrays frameA p.room (by simp)
 obtain sourceA := generator.after_inscr inA restA
 obtain spaceA := space.after restA
 obtain ctxA := (arrays_header frameA (by decide)).trans context
 obtain domA := (arrays_header frameA (by decide)).trans domain
 obtain lenA := (arrays_header frameA (by decide)).trans length
 obtain rowsA := (arrays_header frameA (by decide)).trans rows
 rw [regroup,WP.seq_iff]
 refine WP.mono (storeLiteral_ok powerA.good spaceA ctxA (by decide : 6<8) (by decide : 0<32)) ?_
 rintro b ⟨goodB,valueB,frameB,sameB,restB⟩
 obtain powerB := powerA.after_workspace goodB sameB
 obtain sourceB := sourceA.after_entry frameB (by decide) restB
 obtain spaceB := spaceA.after restB
 obtain ctxB := (workspace_header powerA.good sameB (by decide : sCtx<32)).trans ctxA
 obtain domB := (workspace_header powerA.good sameB (by decide : sDom<32)).trans domA
 obtain lenB := (workspace_header powerA.good sameB (by decide : sLen<32)).trans lenA
 obtain rowsB := (workspace_header powerA.good sameB (by decide : sRows<32)).trans rowsA
 obtain entryB : wv b.mem p.ctx (entryOffset p.w 0) p.w=entryValue p 0 := by
  unfold entryValue
  rw [valueB,powerA.value,VG.Proof.Rsa.FixedBaseComb.exponent_zero]
 obtain tableB : TablePrefix p 1 b :=
  TablePrefix.extend (fun j hj => by omega : TablePrefix p 0 a) (by decide) frameB entryB
 rw [regroup,WP.seq_iff]
 refine WP.mono (generatorLoad_ok goodB sourceB words positive size domB lenB) ?_
 rintro c ⟨goodC,generatorC,frameC,restC⟩
 obtain powerC := powerB.after_arrays goodC frameC (by decide) (by decide) (by decide) (by decide)
 obtain spaceC := spaceB.after restC
 obtain tableC := tableB.after_inscr spaceB (by decide) (InScr.of_arrays frameC p.room (by simp))
 obtain ctxC := (arrays_header frameC (by decide)).trans ctxB
 obtain rowsC := (arrays_header frameC (by decide)).trans rowsB
 rw [WP.seq_iff]
 refine WP.mono (generator_basis M powerC.toModState generatorC reduced) ?_
 rintro d ⟨basisD,frameD,restD⟩
 obtain spaceD := spaceC.after restD
 obtain tableD := tableC.after_inscr spaceC (by decide) (InScr.of_arrays frameD p.room (by simp))
 obtain ctxD := (arrays_header frameD (by decide)).trans ctxC
 obtain rowsD := (arrays_header frameD (by decide)).trans rowsC
 refine WP.mono (storeLiteral_ok basisD.good spaceD ctxD (by decide : 5<8) (by decide : 1<32)) ?_
 rintro t ⟨goodT,valueT,frameT,sameT,restT⟩
 obtain basisT := basisD.after_workspace goodT sameT
 obtain oneExponent : Spec.Rsa.FixedBaseComb.exponent p.N 1=1 := by
  simpa only [Nat.pow_zero,Nat.zero_mul] using VG.Proof.Rsa.FixedBaseComb.exponent_tooth p.N 0 (by decide)
 obtain entryT : wv t.mem p.ctx (entryOffset p.w 1) p.w=entryValue p 1 := by
  unfold entryValue
  rw [valueT,basisD.value,oneExponent]
 obtain tableT := tableD.extend (by decide : 1<32) frameT entryT
 obtain frames : BuildFrame p s.mem t.mem :=
  ((((BuildFrame.of_inscr inA).trans (BuildFrame.of_entry (by decide : 0<32) frameB)).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameC p.room (by simp)))).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameD p.room (by simp)))).trans
    (BuildFrame.of_entry (by decide : 1<32) frameT)
 exact ⟨basisT,spaceD.after restT,(workspace_header basisD.good sameT (by decide : sCtx<32)).trans ctxD,
  (workspace_header basisD.good sameT (by decide : sRows<32)).trans rowsD,tableT,frames,
  ((((restA.trans restB).trans restC).trans restD).trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.TableTiming`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.BasisTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.ProductTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.ProductIOTiming`, which only this module used -/

section

/-! Subset entry transfers use only the public tooth and subset indices. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ProductIO where
 p : Parameters
 j : Nat
 d : Nat

structure ProductIOReady (q : ProductIO) (s : State) : Prop where
 good : Good s q.p.B q.p.Z q.p.w q.p.mi
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 index : word s.mem q.p.B (8*sJ)=BitVec.ofNat 64 q.j
 tooth : word s.mem q.p.B (8*sD)=BitVec.ofNat 64 q.d

theorem productLoad_ct : RelCT isa (Two ProductIOReady) Precompute.productLoad (fun _ _ =>True) := by
 unfold Precompute.productLoad
 refine RelCT.seq (two_piece (Ψ:=fun q s =>EntryReady (q.p,q.j) s) [.x0] ?_ (by taint_decide) ?_)
  (two_map (fun q =>(q.p,q.j)) (fun _ _ h =>h) (loadEntry_ct 1 (by decide) (by taint_decide)))
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.good.x0.trans ht.good.x0.symm
 · intro q s h
   refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 q.j ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [h.good.x0,hdr_enc (show sJ<32 by decide),header_read h.good q.p.room (show sJ<32 by decide),h.index]
   · rintro t ⟨⟨index,mem⟩,rest⟩
     exact ⟨⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,
      mem ▸ h.context,index⟩

theorem productStore_ct : RelCT isa (Two ProductIOReady) Precompute.productStore (fun _ _ =>True) := by
 unfold Precompute.productStore
 refine RelCT.seq (two_piece (Ψ:=fun q s =>EntryReady (q.p,q.j+q.d) s) [.x0] ?_ (by taint_decide) ?_)
  (two_map (fun q =>(q.p,q.j+q.d)) (fun _ _ h =>h) (storeEntry_ct 6 (by decide) (by taint_decide)))
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.good.x0.trans ht.good.x0.symm
 · intro q s h
   refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 (q.j+q.d) ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [h.good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
      header_read h.good q.p.room (show sJ<32 by decide),header_read h.good q.p.room (show sD<32 by decide),
      h.index,h.tooth,←BitVec.ofNat_add]
   · rintro t ⟨⟨index,mem⟩,rest⟩
     exact ⟨⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,
      mem ▸ h.context,index⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

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
   refine WP.mono (productLoad_ok h.2.basis.good h.2.space h.2.context h.2.index (by have := h.2.limit;have := Nat.two_pow_pos q.b;omega_arith)) ?_
   rintro t ⟨good,selected,frame,rest⟩
   have basis := h.2.basis.after_arrays good frame (by decide) (by decide) (by decide) (by decide)
   have state := h.2.after_arrays basis frame rest (by simp)
   exact ⟨⟨h.1,state⟩,selected.trans (h.2.table q.j (by have := h.2.position;have := Nat.two_pow_pos q.b;omega_arith))⟩
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
        have bound : 2^q.b≤16 := Nat.pow_le_pow_right (by decide) (by have := h.2.tooth;omega_using [this] : q.b≤4)
        have := h.1
        omega_using [bound, this]
       refine WP.mono (productStore_ok h.2.basis.good h.2.space h.2.context h.2.index h.2.basisIndex destination) ?_
       rintro t ⟨good,_,_,_,_⟩
       exact good.x0
     · intro q s t hs ht r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.trans ht.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SquaresTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SquareTiming`, which only this module used -/

section

/-! Comb-table squaring uses a public row count with independent residue values. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure SquarePublic where
 p : Parameters
 n : Nat
 positive : 0<n
 fit : n<2^64

def SquareReady (q : SquarePublic) (j : Nat) (s : State) : Prop :=
 ∃ E,Power q.p E s ∧ Counter q.p.B (q.n-j) s

theorem squareStep_ct (M : Mont) :
 RelCT isa (Two fun (q : SquarePublic × Nat) s => SquareReady q.1 q.2 s)
 (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI])) (fun _ _ => True) := by
 refine RelCT.seq (two_post (Ψ:=fun (q : SquarePublic × Nat) s =>SquareReady q.1 q.2 s)
  (two_map (fun q => (⟨q.1.p.B,q.1.p.Z,q.1.p.w⟩ : Ws))
   (fun q s h =>by obtain ⟨E,power,_⟩:=h;exact ⟨q.1.p.mi,power.good,q.1.p.room⟩)
   (M.ct (by simp [MmUse,Public.aY]))) ?_) (two_taint [.x0] ?_ (by taint_decide))
 · rintro ⟨q,j⟩ s ⟨E,power,counter⟩
   refine WP.mono (power_square M power) ?_
   rintro t ⟨powerT,frame,_⟩
   exact ⟨2*E,powerT,(arrays_header frame (by decide)).trans counter⟩
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   obtain ⟨E,power,_⟩ := hs
   obtain ⟨F,other,_⟩ := ht
   exact power.good.x0.trans other.good.x0.symm

theorem squareLoop_ct (M : Mont) :
 RelCT isa (Two fun q s =>SquareReady q 0 s)
 (.loop (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI]))
  (.nonzero .x .x3)) (fun _ _ => True) := by
 have loop := two_loop (cond:= .nonzero .x .x3) (Φ:=SquareReady) (Ψ:=fun _ _ =>True) (fun q =>q.n)
  ((squareStep_ct M).mono (fun _ _ h =>two_mono (fun _ _ h =>h.2) h) (fun _ _ h =>h)) (by
   intro q j s hj h
   obtain ⟨E,power,counter⟩ := h
   have initial : SquareInv s q.p E (q.n-j) 0 s :=
    ⟨by simpa using power,by simpa using counter,Frm.refl _ _ _,VG.Proof.MlKem.AArch64.Keep.refl _ _⟩
   refine WP.mono (precomputeSquareStep M (by have := q.fit;omega_using [this]) (by omega_using [hj] : 0<q.n-j) initial) ?_
   rintro t ⟨state,branch⟩
   refine ⟨?_,fun _ =>⟨_,state.power,?_⟩,fun _ =>trivial⟩
   · rw [eval_nonzero,ne_zero_iff]
     have eq : (0+1≠q.n-j) ↔ j+1<q.n := by omega_using [hj]
     by_cases nonzero : (t.gpr .x3).toNat≠0
     · rw [decide_eq_true nonzero,decide_eq_true ((branch.trans eq).mp nonzero)]
     · have last : ¬j+1<q.n := fun h =>nonzero ((branch.trans eq).mpr h)
       rw [decide_eq_false nonzero,decide_eq_false last]
   · change Counter q.p.B (q.n-(j+1)) t
     have eq : q.n-j-(0+1)=q.n-(j+1) := by omega_using []
     simpa only [eq] using state.counter)
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨q.positive,hs⟩,⟨q.positive,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Advance a tooth with two fixed copies and a public-count squaring loop. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def SquareBasisReady (q : SquarePublic) (s : State) : Prop :=
 ∃ E,Basis q.p E s ∧ word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 q.n

def SquareCounterReady (q : SquarePublic) (s : State) : Prop :=
 ∃ E,Power q.p E s ∧ word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 q.n

def squareWs (q : SquarePublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem precomputeSquares_ct (M : Mont) :
 RelCT isa (Two SquareBasisReady) (Precompute.squares M.mm) (fun _ _ =>True) := by
 unfold Precompute.squares
 refine RelCT.seq (two_post (Ψ:=SquareCounterReady)
  (two_map squareWs (fun q s h => by obtain ⟨E,basis,_⟩:=h;exact ⟨q.p.mi,basis.good,q.p.room⟩)
   (copy_ct (by decide : 6<8) (by decide : 5<8) (by taint_decide))) ?_) ?_
 · rintro q s ⟨E,basis,rows⟩
   refine WP.mono (basis_to_power basis) ?_
   rintro t ⟨power,_,frame,_⟩
   exact ⟨E,power,(arrays_header frame (by decide)).trans rows⟩
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>SquareReady q 0 s) [.x0] ?_ (by taint_decide) ?_) ?_
   · intro q s t hs ht r hr
     have eq : r= .x0 := by simpa using hr
     subst r
     obtain ⟨E,power,_⟩ := hs
     obtain ⟨F,other,_⟩ := ht
     exact power.good.x0.trans other.good.x0.symm
   · rintro q s ⟨E,power,rows⟩
     refine WP.mono (counterInit_ok power.good q.p.room rows) ?_
     rintro t ⟨good,counter,frame,_⟩
     exact ⟨E,power.after_header good frame (by decide),by simpa using counter⟩
   · refine RelCT.seq (two_post (Ψ:=fun q s =>GoodW (squareWs q) s) (squareLoop_ct M) ?_)
      (two_map squareWs (fun _ _ h =>h) (copy_ct (by decide : 5<8) (by decide : 6<8) (by taint_decide)))
     rintro q s ⟨E,power,counter⟩
     refine WP.mono (precomputeSquareLoop_ok M power (by simpa using counter) q.positive q.fit) ?_
     rintro t ⟨power,_,_,_⟩
     exact ⟨q.p.mi,power.good,q.p.room⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

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

end

end

/-! ### `Ffdh.AArch64.Cached.InitialTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.InitialTimingParts`, which only this module used -/

section

/-! Fixed-index stores, field initialization, and generator loading have public traces. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def fieldWs (p : Parameters) : Ws := ⟨p.B,p.Z,p.w⟩

theorem fieldPowerInit_ct (M : Mont) : RelCT isa (Two FieldInitial)
 (.seq (const 7 1) (M.mm 6 4 7)) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=fun p s =>GoodW (fieldWs p) s)
  (two_map fieldWs (fun p s h =>⟨p.mi,h.good,p.room⟩) (const_ct 7 1 (by decide) (by taint_decide) (by taint_decide))) ?_)
  (two_map fieldWs (fun _ _ h =>h) (M.ct (by simp [MmUse,Public.aY,Public.aR2,Public.aOne])))
 intro p s h
 exact WP.mono (const_ok h.good p.room (by have :=p.positive;omega_using [this]) p.width (by decide : 7<8) (by decide : 1<2^16))
  (fun _ ⟨good,_,_,_⟩ =>⟨p.mi,good,p.room⟩)

def LiteralReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ word s.mem p.B (8*sCtx)=p.ctx

theorem storeLiteral_ct {a d : Nat} (array : a<8) (small : d<2^16)
 {hc hd : VG.Taint.Hint VG.AArch64.Taint.T}
 (head : (taint.check (Taint.ofRegs []) (.block [movi .x3 d]) hc).isSome=true)
 (tail : (taint.check (Taint.ofRegs [.x0,.x3]) (.block (entryPtr++[ldh .x16 (sArr a)])) hd).isSome=true) :
 RelCT isa (Two LiteralReady) (.seq (.block [movi .x3 d]) (storeEntry a)) (fun _ _ =>True) := by
 refine RelCT.seq (two_piece (Ψ:=fun p s =>EntryReady (p,d) s) [] (fun _ _ _ _ _ r hr =>by simp at hr) head ?_)
  (two_map (fun p =>(p,d)) (fun _ _ h =>h) (storeEntry_ct a array tail))
 rintro p s ⟨good,ctx⟩
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 d ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [movi_nat small]
 · rintro t ⟨⟨digit,mem⟩,rest⟩
   exact ⟨⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,mem ▸ ctx,digit⟩

structure GeneratorPublic where
 p : Parameters
 dom : Addr

structure GeneratorReady (q : GeneratorPublic) (s : State) : Prop where
 good : Good s q.p.B q.p.Z q.p.w q.p.mi
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

theorem generatorLoad_ct : RelCT isa (Two GeneratorReady)
 (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) (fun _ _ =>True) := by
 refine RelCT.seq (two_piece (Ψ:=fun q s =>LoadReady (⟨fieldWs q.p,q.dom+BitVec.ofNat 64 q.p.k,q.p.k⟩ : LoadPublic) s) [.x0]
  (fun q s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r;exact hs.good.x0.trans ht.good.x0.symm) (by taint_decide) ?_)
  (two_map (fun q =>(⟨fieldWs q.p,q.dom+BitVec.ofNat 64 q.p.k,q.p.k⟩ : LoadPublic)) (fun _ _ h =>h)
   (load_ct (by decide : 1<8) (by taint_decide)))
 intro q s h
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
  t.gpr .x1=q.dom+BitVec.ofNat 64 q.p.k ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [h.good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read h.good q.p.room (show sDom<32 by decide),header_read h.good q.p.room (show sLen<32 by decide),h.domain,h.length]
 · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
   exact ⟨⟨q.p.mi,⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,q.p.room⟩,ptr,len⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.InitialTimingState`, which only this module used -/

section

/-! Field and immutable-domain state across the table initializer. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure InitialPublic where
 p : Parameters
 dom : Addr
 bs : List Byte
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 reduced : p.G<p.P

structure TableInitialReady (q : InitialPublic) (s : State) : Prop where
 field : FieldInitial q.p s
 space : ContextSpace q.p s
 generator : GeneratorSource q.p (q.dom+BitVec.ofNat 64 q.p.k) q.bs s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

structure InitialWorking (q : InitialPublic) (s : State) : Prop where
 state : ModState q.p s
 space : ContextSpace q.p s
 generator : GeneratorSource q.p (q.dom+BitVec.ofNat 64 q.p.k) q.bs s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

theorem initialOne_working (M : Mont) {q : InitialPublic} {s : State} (h : TableInitialReady q s) :
 WP isa (.seq (const 7 1) (M.mm 6 4 7)) s (InitialWorking q) := by
 refine WP.mono (field_initial_power M h.field) ?_
 rintro t ⟨power,frame,rest⟩
 exact ⟨power.toModState,h.space.after rest,h.generator.after_inscr (InScr.of_arrays frame q.p.room (by simp)) rest,
  (arrays_header frame (by decide)).trans h.context,(arrays_header frame (by decide)).trans h.domain,
  (arrays_header frame (by decide)).trans h.length⟩

theorem initialZero_stored {q : InitialPublic} {s : State} (h : InitialWorking q s) :
 WP isa (.seq (.block [movi .x3 0]) (storeEntry 6)) s (InitialWorking q) := by
 refine WP.mono (storeLiteral_ok h.state.good h.space h.context (by decide : 6<8) (by decide : 0<32)) ?_
 rintro t ⟨good,_,frame,same,rest⟩
 have field : FieldInitial q.p s := ⟨h.state.good,h.state.modulus,h.state.inverse,h.state.r2⟩
 have next :=field.after_workspace good same
 have one :=(workspace_array h.state.good same (by decide : 7<8)).trans h.state.one
 have state : ModState q.p t :=⟨next.good,next.modulus,next.inverse,one,next.r2⟩
 exact ⟨state,h.space.after rest,h.generator.after_entry frame (by decide) rest,
  (workspace_header h.state.good same (by decide)).trans h.context,
  (workspace_header h.state.good same (by decide)).trans h.domain,
  (workspace_header h.state.good same (by decide)).trans h.length⟩

/-- Input to the generator-to-Montgomery conversion. -/
def GeneratorLoaded (q : InitialPublic) (s : State) : Prop :=
 InitialWorking q s ∧ wv s.mem q.p.B (slot q.p.w 1) q.p.w=q.p.G

theorem initialGenerator_loaded {q : InitialPublic} {s : State} (h : InitialWorking q s) :
 WP isa (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) s (GeneratorLoaded q) := by
 refine WP.mono (generatorLoad_ok h.state.good h.generator q.words q.positive q.size h.domain h.length) ?_
 rintro t ⟨good,value,frame,rest⟩
 exact ⟨⟨h.state.after_arrays good frame (by decide) (by decide) (by decide),h.space.after rest,
  h.generator.after_inscr (InScr.of_arrays frame q.p.room (by simp)) rest,
  (arrays_header frame (by decide)).trans h.context,(arrays_header frame (by decide)).trans h.domain,
  (arrays_header frame (by decide)).trans h.length⟩,value⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete public table initializer uses fixed indices zero and one. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeInitial_ct (M : Mont) : RelCT isa (Two TableInitialReady) (Precompute.initial M.mm) (fun _ _ =>True) := by
 unfold Precompute.initial
 simp only [seqs]
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitialWorking)
  (two_map InitialPublic.p (fun _ _ h =>h.field) (fieldPowerInit_ct M))
  (fun _ _ h =>initialOne_working M h)) ?_
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitialWorking)
  (two_map InitialPublic.p (fun _ _ h =>⟨h.state.good,h.context⟩)
   (storeLiteral_ct (by decide : 6<8) (by decide : 0<2^16) (by taint_decide) (by taint_decide)))
  (fun _ _ h =>initialZero_stored h)) ?_
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=GeneratorLoaded)
  (two_map (fun q =>(⟨q.p,q.dom⟩ : GeneratorPublic)) (fun _ _ h =>⟨h.state.good,h.domain,h.length⟩) generatorLoad_ct)
  (fun _ _ h =>initialGenerator_loaded h)) ?_
 refine RelCT.seq (two_post (Ψ:=fun q s =>LiteralReady q.p s)
  (two_map (fun q =>fieldWs q.p) (fun q s h =>⟨q.p.mi,h.1.state.good,q.p.room⟩)
   (M.ct (by simp [MmUse,Public.aXm,Public.aX,Public.aR2]))) ?_)
  (two_map InitialPublic.p (fun _ _ h =>h)
   (storeLiteral_ct (by decide : 5<8) (by decide : 1<2^16) (by taint_decide) (by taint_decide)))
 intro q s h
 refine WP.mono (generator_basis M h.1.state h.2 q.reduced) ?_
 rintro t ⟨basis,frame,_⟩
 exact ⟨basis.good,(arrays_header frame (by decide)).trans h.1.context⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeTable`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeBasisLoop`, which this module and modules that import it used -/

section

/-! Four fixed public rounds finish all 32 canonical comb entries. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

private theorem basisCounterFlag : ∀ i<4,
 ((BitVec.ofNat 64 (2^((i+1)+1))-32#64).toNat≠0 ↔ i+1≠4) := by decide +kernel

theorem precomputeBasisLoop_ok (M : Mont) {s : State} {p : Parameters} (h : BasisState p 1 s) :
 WP isa (.loop (Precompute.basis M.mm) (.nonzero .x .x3)) s fun t =>
 BasisState p 5 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 let I := fun i t => BasisState p (i+1) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t
 refine WP.mono (count_loop (by decide : 0<4) I (fun i hi t inv => ?_)
  ⟨h,Frame.refl _ _,Keep.refl _ _⟩) ?_
 · refine WP.mono (precomputeBasis_ok M inv.1 (by omega_using [hi] : i+1<5)) ?_
   rintro u ⟨state,index,frame,rest⟩
   refine ⟨⟨state,inv.2.1.trans frame,(inv.2.2.trans rest).mono (by simp [mmRegs])⟩,?_⟩
   rw [index]
   exact basisCounterFlag i hi
 · rintro t ⟨state,frame,rest⟩
   exact ⟨state,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Complete verified construction of the canonical 32-entry comb table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeTable_ok (M : Mont) {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (generator : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P) (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=dom)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) :
 WP isa (Precompute.table M.mm) s fun t =>
 BasisState p 5 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.table
 rw [WP.seq_iff]
 refine WP.mono (precomputeInitial_ok M field space generator words positive size reduced context domain length rows) ?_
 rintro a ⟨basisA,spaceA,ctxA,rowsA,tableA,frameA,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (setControlNat_ok basisA.good p.room (by decide : 16≤sD) (by decide : sD<32) (by decide : 2<2^16)) ?_
 rintro b ⟨goodB,indexB,frameB,restB⟩
 have inB : InScr p.B p.Z a.mem b.mem :=
  InScr.of_outside frameB (by have := hdr_lt_slot p.w 8 (show sD<32 by decide);have := p.room;omega_arith)
 have basisB := basisA.after_header goodB frameB (by decide : sD<32)
 have stateB : BasisState p 1 b :=
  ⟨⟨by decide,by decide⟩,bits,(by simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using basisB),spaceA.after restB,
   (header_other frameB (by decide) (by decide) (by decide)).trans ctxA,indexB,
   (header_other frameB (by decide) (by decide) (by decide)).trans rowsA,
   tableA.after_inscr spaceA (by decide) inB⟩
 refine WP.mono (precomputeBasisLoop_ok M stateB) ?_
 rintro t ⟨state,frame,rest⟩
 exact ⟨state,(frameA.trans (BuildFrame.of_inscr inB)).trans frame,
  ((restA.trans restB).trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.BasisLoopTiming`, which only this module used -/

section

/-! The public table completes exactly four tooth rounds. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure BasisLoopPublic where
 p : Parameters
 bits : 0<p.N ∧ p.N≤8192

def BasisLoopReady (q : BasisLoopPublic) (i : Nat) (s : State) : Prop := BasisState q.p (i+1) s

private theorem basisFlag : ∀ i<4,
 (BitVec.ofNat 64 (2^((i+1)+1))-32#64 !=0#64)=decide (i+1<4) := by decide +kernel

theorem precomputeBasisLoop_ct (M : Mont) : RelCT isa (Two fun q s =>BasisLoopReady q 0 s)
 (.loop (Precompute.basis M.mm) (.nonzero .x .x3)) (fun _ _ =>True) := by
 have hct : RelCT isa (Two fun (q : BasisLoopPublic × Fin 4) s =>BasisLoopReady q.1 q.2.val s)
  (Precompute.basis M.mm) (fun _ _ =>True) :=
  two_map (fun q =>(⟨q.1.p,q.2.val+1,by omega_using [],by have :=q.2.isLt;omega_using [],q.1.bits⟩ : BasisPublic))
   (fun _ _ h =>h) (precomputeBasis_ct M)
 have stepCt : RelCT isa (Two fun (q : BasisLoopPublic × Nat) s =>q.2<4 ∧ BasisLoopReady q.1 q.2 s)
  (Precompute.basis M.mm) (fun _ _ =>True) := by
  intro s t ts tt u v h es et
  obtain ⟨⟨q,i⟩,⟨hi,hs⟩,⟨_,ht⟩,sp⟩:=h
  exact hct _ _ _ _ _ _ ⟨(q,⟨i,hi⟩),hs,ht,sp⟩ es et
 have loop:=two_loop (cond:= .nonzero .x .x3) (Φ:=BasisLoopReady) (Ψ:=fun _ _ =>True)
  (fun _ : BasisLoopPublic =>4) stepCt (by
   intro q i s hi h
   refine WP.mono (precomputeBasis_ok M h (by omega_using [hi] : i+1<5)) ?_
   rintro t ⟨state,index,_,_⟩
   refine ⟨?_,fun _ =>state,fun _ =>trivial⟩
   rw [eval_nonzero,index]
   exact congrArg some (basisFlag i hi))
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨by decide,hs⟩,⟨by decide,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! All 32 public comb entries are built on a fixed public schedule. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure TablePublic extends InitialPublic where
 bits : 0<p.N ∧ p.N≤8192

structure TableReady (q : TablePublic) (s : State) : Prop extends TableInitialReady q.toInitialPublic s where
 rows : word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N)

structure TableInitialized (q : TablePublic) (s : State) : Prop where
 basis : Basis q.p 1 s
 space : ContextSpace q.p s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 rows : word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N)
 table : TablePrefix q.p 2 s

theorem precomputeTable_ct (M : Mont) : RelCT isa (Two TableReady) (Precompute.table M.mm) (fun _ _ =>True) := by
 unfold Precompute.table
 refine RelCT.seq (two_post (Ψ:=TableInitialized)
  (two_map TablePublic.toInitialPublic (fun _ _ h =>h.toTableInitialReady) (precomputeInitial_ct M)) ?_) ?_
 · intro q s h
   exact WP.mono (precomputeInitial_ok M h.field h.space h.generator q.words q.positive q.size q.reduced h.context h.domain h.length h.rows)
    (fun _ ⟨basis,space,ctx,rows,table,_,_⟩ =>⟨basis,space,ctx,rows,table⟩)
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>BasisLoopReady (⟨q.p,q.bits⟩ : BasisLoopPublic) 0 s) [.x0]
    (fun q s t hs ht r hr =>by
     have eq : r= .x0 := by simpa using hr
     subst r;exact hs.basis.good.x0.trans ht.basis.good.x0.symm) (by taint_decide) ?_)
    (two_map (fun q =>(⟨q.p,q.bits⟩ : BasisLoopPublic)) (fun _ _ h =>h) (precomputeBasisLoop_ct M))
   intro q s h
   refine WP.mono (setControlNat_ok h.basis.good q.p.room (by decide : 16≤sD) (by decide : sD<32) (by decide : 2<2^16)) ?_
   rintro t ⟨good,index,frame,rest⟩
   have inscr : InScr q.p.B q.p.Z s.mem t.mem :=InScr.of_outside frame
    (by have :=hdr_lt_slot q.p.w 8 (show sD<32 by decide);have :=q.p.room;omega_arith)
   refine ⟨⟨by decide,by decide⟩,q.bits,?_,h.space.after rest,
    (header_other frame (by decide) (by decide) (by decide)).trans h.context,index,
    (header_other frame (by decide) (by decide) (by decide)).trans h.rows,h.table.after_inscr h.space (by decide) inscr⟩
   simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using h.basis.after_header good frame (by decide : sD<32)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.StorePrefixTiming`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.StorePrefix`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.CopyToContext`, which only this module used -/

section

/-! Copy one native arithmetic array into a public canonical context span. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem copyToContext_ok {s : State} {p : Parameters} {a n : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s) (array : a<8) (span : n+p.w≤3+34*p.w)
 (source : s.gpr .x16=off p.B (slot p.w a)) (output : s.gpr .x17=off p.ctx (8*n))
 (count : s.gpr .x12=BitVec.ofNat 64 p.w) :
 WP isa copyWords s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.ctx (8*n) p.w=wv s.mem p.B (slot p.w a) p.w ∧
 Outside p.ctx (8*n) (8*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ t.gpr .x17=off p.ctx (8*(n+p.w)) ∧ Keep mmRegs s t := by
 have arrayRoom : slot p.w a+8*(p.w+2)≤p.Z := Nat.le_trans (slot_le array) p.room
 have fit : 8*n+8*p.w≤2^64 := by have := p.width;omega_using [span, this]
 have offFit : 8*n<2^64 := by have := p.positive;omega_using [span, fit]
 have outside (i : Nat) (hi : i<8*p.w) : p.Z≤ofs p.B (off p.ctx (8*n)+BitVec.ofNat 64 i) := by
  have h := space.outside (8*n+i) (by omega_using [span, hi])
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using h
 have sourceInside (i : Nat) (hi : i<p.w) (b : Nat) (hb : b<8) :
  ofs p.B (off p.B (slot p.w a+8*i)+BitVec.ofNat 64 b)<p.Z := by
  rw [ofs_off p.B (by have := good.scr.nowrap;omega_using [arrayRoom, hi, hb, this])]
  omega_using [arrayRoom, hi, hb]
 refine WP.mono (copyWords_ok source output count (by have := p.positive;omega_using [this]) p.width fit
  (fun i hi => good.scr.ld (by omega_using [arrayRoom, hi]))
  (fun i hi => by
   have rd := space.writable (n+i) (by omega_using [span, hi])
   simpa only [Nat.mul_add] using rd)
  (fun i hi b hb => (outside_shift_iff p.ctx _ offFit fit).mpr (le_ofs_of_sep outside (sourceInside i hi b hb)))) ?_
 rintro t ⟨value,_,frame,_,pointer,rest⟩
 have unchanged (x : Addr) (hx : ofs p.B x<p.Z) : t.mem x=s.mem x :=
  frame x ((outside_shift_iff p.ctx x offFit fit).mpr (le_ofs_of_sep outside hx))
 have header (i : Nat) (hi : i<32) : word t.mem p.B (8*i)=word s.mem p.B (8*i) :=
  workspace_header good unchanged hi
 have totalRest : Keep mmRegs s t := rest.mono (by simp [mmRegs])
 refine ⟨⟨good.scr.congr totalRest.wr,(totalRest.gpr .x0 (by simp [mmRegs])).trans good.x0,
  (header sW (by decide)).trans good.hdr.hw,(header sMinv (by decide)).trans good.hdr.hminv,
  fun i hi => (header (sArr i) (by unfold sArr;omega_using [hi])).trans (good.hdr.harr i hi)⟩,
  value,frame,unchanged,?_,totalRest⟩
 simpa only [Nat.mul_add] using pointer

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Store p and R² after the three canonical metadata words. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem storePrefix_ok {s : State} {p : Parameters} (h : FieldInitial p s) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) :
 WP isa Precompute.storePrefix s fun t =>
 FieldInitial p t ∧ wv t.mem p.ctx 24 p.w=p.P ∧
 wv t.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P ∧
 Outside p.ctx 24 (16*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 unfold Precompute.storePrefix
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x12,.x16,.x17] (Q:=fun a =>a.gpr .x16=off p.B (slot p.w 0) ∧
  a.gpr .x17=off p.ctx 24 ∧ a.gpr .x12=BitVec.ofNat 64 p.w ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [h.good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
    header_read h.good p.room (show sCtx<32 by decide),header_read h.good p.room (show sArr 0<32 by decide),
    header_read h.good p.room (show sW<32 by decide),context,h.good.hdr.harr 0 (by decide),h.good.hdr.hw]
 · rintro a ⟨⟨srcA,dstA,countA,memA⟩,restA⟩
   have goodA : Good a p.B p.Z p.w p.mi :=
    ⟨h.good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans h.good.x0,memA ▸ h.good.hdr⟩
   rw [WP.seq_iff]
   refine WP.mono (copyToContext_ok goodA (space.after restA) (by decide : 0<8) (by omega_using [] : 3+p.w≤3+34*p.w)
    srcA dstA countA) ?_
   rintro b ⟨goodB,valueB,frameB,sameB,pointerB,restB⟩
   have sameBS (x : Addr) (hx : ofs p.B x<p.Z) : b.mem x=s.mem x := by rw [sameB x hx,memA]
   have fieldB := h.after_workspace goodB sameBS
   have spaceB := (space.after restA).after restB
   have firstValue : wv b.mem p.ctx 24 p.w=p.P := by rw [valueB,memA];exact h.modulus
   rw [WP.seq_iff]
   refine WP.mono (WP.keep [.x12,.x16] (Q:=fun c =>c.gpr .x16=off p.B (slot p.w 4) ∧
    c.gpr .x12=BitVec.ofNat 64 p.w ∧ c.mem=b.mem) ?_ rfl rfl rfl) ?_
   · brun [goodB.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
      header_read goodB p.room (show sArr 4<32 by decide),header_read goodB p.room (show sW<32 by decide),
      goodB.hdr.harr 4 (by decide),goodB.hdr.hw]
   · rintro c ⟨⟨srcC,countC,memC⟩,restC⟩
     have goodC : Good c p.B p.Z p.w p.mi :=
      ⟨goodB.scr.congr restC.wr,(restC.gpr .x0 (by decide)).trans goodB.x0,memC ▸ goodB.hdr⟩
     refine WP.mono (copyToContext_ok goodC (spaceB.after restC) (by decide : 4<8) (by omega_using [] : 3+p.w+p.w≤3+34*p.w)
      srcC ((restC.gpr .x17 (by decide)).trans pointerB) countC) ?_
     rintro t ⟨goodT,valueT,frameT,sameT,_,restT⟩
     have sameTS (x : Addr) (hx : ofs p.B x<p.Z) : t.mem x=s.mem x := by
      rw [sameT x hx,memC]
      exact sameBS x hx
     have fieldT := h.after_workspace goodT sameTS
     have secondValue : wv t.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P := by
      have rhs : wv c.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P := by rw [memC];exact fieldB.r2
      simpa only [Nat.mul_add] using valueT.trans rhs
     have frameTC : Outside p.ctx (24+8*p.w) (8*p.w) c.mem t.mem := by
      simpa only [Nat.mul_add] using frameT
     have firstT : wv t.mem p.ctx 24 p.w=p.P := by
      rw [frameTC.wv (Or.inl (by omega_using [])) (by have := p.width;omega_using [this]),memC]
      exact firstValue
     have frameBS : Outside p.ctx 24 (8*p.w) s.mem b.mem := by rw [←memA];exact frameB
     have frameTS : Outside p.ctx 24 (16*p.w) s.mem t.mem := by
      intro x hx
      rw [frameTC x (by omega_using [hx]),memC]
      exact frameBS x (by omega_using [hx])
     exact ⟨fieldT,firstT,secondValue,frameTS,sameTS,
      (((restA.trans restB).trans restC).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Serialization copies two complete public-length limb ranges to fixed context offsets. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def StorePrefixReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ ContextSpace p s ∧ word s.mem p.B (8*sCtx)=p.ctx

def StoreFirstReady (p : Parameters) (s : State) : Prop :=
 StorePrefixReady p s ∧ s.gpr .x16=off p.B (slot p.w 0) ∧ s.gpr .x17=off p.ctx 24 ∧ s.gpr .x12=BitVec.ofNat 64 p.w

def StoreSecondReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ s.gpr .x17=off p.ctx (24+8*p.w)

theorem storePrefix_ct : RelCT isa (Two StorePrefixReady) Precompute.storePrefix (fun _ _ =>True) := by
 unfold Precompute.storePrefix
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=StoreFirstReady) [.x0] (fun p s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.1.x0.trans ht.1.x0.symm) (by taint_decide) ?_) ?_
 · rintro p s ⟨good,space,ctx⟩
   refine WP.mono (WP.keep [.x12,.x16,.x17] (Q:=fun t =>t.gpr .x16=off p.B (slot p.w 0) ∧
    t.gpr .x17=off p.ctx 24 ∧ t.gpr .x12=BitVec.ofNat 64 p.w ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
      header_read good p.room (show sCtx<32 by decide),header_read good p.room (show sArr 0<32 by decide),
      header_read good p.room (show sW<32 by decide),ctx,good.hdr.harr 0 (by decide),good.hdr.hw]
   · rintro t ⟨⟨ptr,dst,count,mem⟩,rest⟩
     exact ⟨⟨⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,
      space.after rest,mem ▸ ctx⟩,ptr,dst,count⟩
 · refine RelCT.seq (two_post (Ψ:=StoreSecondReady)
    (two_taint [.x16,.x17,.x12] (fun _ s t hs ht r hr =>by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl
     · exact hs.2.1.trans ht.2.1.symm
     · exact hs.2.2.1.trans ht.2.2.1.symm
     · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)) ?_) ?_
   · rintro p s ⟨⟨good,space,_⟩,src,dst,count⟩
     refine WP.mono (copyToContext_ok good space (by decide : 0<8) (by omega_using [] : 3+p.w≤3+34*p.w) src dst count) ?_
     rintro t ⟨good,_,_,_,ptr,_⟩
     exact ⟨good,by simpa only [Nat.mul_add,Nat.reduceMul] using ptr⟩
   · refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x16=off p.B (slot p.w 4) ∧
      s.gpr .x17=off p.ctx (24+8*p.w) ∧ s.gpr .x12=BitVec.ofNat 64 p.w) [.x0]
      (fun p s t hs ht r hr =>by
       have eq : r= .x0 := by simpa using hr
       subst r;exact hs.1.x0.trans ht.1.x0.symm) (by taint_decide) ?_)
      (two_taint [.x16,.x17,.x12] (fun _ s t hs ht r hr =>by
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl|rfl
       · exact hs.1.trans ht.1.symm
       · exact hs.2.1.trans ht.2.1.symm
       · exact hs.2.2.trans ht.2.2.symm) (by taint_decide))
     rintro p s ⟨good,ptr⟩
     brun [good.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
      header_read good p.room (show sArr 4<32 by decide),header_read good p.room (show sW<32 by decide),
      good.hdr.harr 4 (by decide),good.hdr.hw,ptr]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.GeneratorContextFrame`, which only this module used -/

section

/-! A public generator source is disjoint from every portion of the writable context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem GeneratorSource.after_context {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg} {d n : Nat}
 (h : GeneratorSource p ptr bs s) (frame : Outside p.ctx d n s.mem t.mem)
 (inside : d+n≤8*(3+34*p.w)) (rest : Keep rs s t) : GeneratorSource p ptr bs t := by
 refine ⟨⟨?_,?_,h.source.out⟩,h.length,h.value,h.separate⟩
 · intro i hi;rw [rest.rd,rest.wr];exact h.source.rd i hi
 · intro i hi
   rw [frame _ (Or.inr (by have :=h.separate i hi;omega_using [inside, this]))]
   exact h.source.val i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete public-context serialization and comb-table tail. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem prefix_table_ready {q : TablePublic} {s : State} (h : TableReady q s) :
 WP isa Precompute.storePrefix s (TableReady q) := by
 refine WP.mono (storePrefix_ok h.field h.space h.context) ?_
 rintro t ⟨field,_,_,frame,same,rest⟩
 have hdr (i : Nat) (hi : i<32) :=workspace_header h.field.good same hi
 exact ⟨⟨field,h.space.after rest,h.generator.after_context frame (by omega_using []) rest,
  (hdr sCtx (by decide)).trans h.context,(hdr sDom (by decide)).trans h.domain,
  (hdr sLen (by decide)).trans h.length⟩,(hdr sRows (by decide)).trans h.rows⟩

theorem precomputeTail_ct (M : Mont) : RelCT isa (Two TableReady)
 (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1]))) (fun _ _ =>True) := by
 refine RelCT.seq (two_post
  (two_map (fun q =>q.p) (fun _ _ h =>⟨h.field.good,h.space,h.context⟩) storePrefix_ct)
  (fun _ _ h =>prefix_table_ready h)) ?_
 refine RelCT.seq (two_post (Ψ:=fun (_ : TablePublic) _ =>True) (precomputeTable_ct M) ?_)
  (two_taint [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide))
 intro q s h
 exact WP.mono (precomputeTable_ok M h.field h.space h.generator q.words q.positive q.size q.reduced q.bits h.context h.domain h.length h.rows)
  (fun _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
