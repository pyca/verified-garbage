module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeArithmetic
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomain
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Metadata
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicFrame
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
/-! Functional composition of the complete native public precomputation routine. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeEntry.lean`, which only this module imported.
section

/-! The native entry saves only public arguments in the scratch header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def entryMemory (m : Mem) (B ctx dom dl k : Addr) : Mem :=
 (((m.writeW (off B (8*sCtx)) ctx).writeW (off B (8*sDom)) dom).writeW
 (off B (8*sDL)) dl).writeW (off B (8*sLen)) k

theorem precomputeEntry_ok {s : State} {B : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x5=B) :
 WP isa (.block Precompute.entry) s fun t =>
 (t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ∧
 Keep [.x0] s t := by
 refine WP.keep [.x0] (Q:=fun t => t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ?_ rfl rfl rfl
 unfold Precompute.entry entryMemory
 brun [base,st,hdr_enc (show sCtx<32 by decide),hdr_enc (show sDom<32 by decide),
  hdr_enc (show sDL<32 by decide),hdr_enc (show sLen<32 by decide),
  scratch.st (d:=8*sCtx) (by unfold sCtx;omega),
  scratch.st (d:=8*sDom) (by unfold sDom;omega),
  scratch.st (d:=8*sDL) (by unfold sDL;omega),
  scratch.st (d:=8*sLen) (by unfold sLen;omega)]

theorem entryMemory_header (m : Mem) (B ctx dom dl k : Addr) :
 word (entryMemory m B ctx dom dl k) B (8*sCtx)=ctx ∧
 word (entryMemory m B ctx dom dl k) B (8*sDom)=dom ∧
 word (entryMemory m B ctx dom dl k) B (8*sDL)=dl ∧
 word (entryMemory m B ctx dom dl k) B (8*sLen)=k := by
 have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
  word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
  Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)
 unfold entryMemory
 rw [separate _ sLen sCtx (by decide) (by decide) (by decide) _,
  separate _ sDL sCtx (by decide) (by decide) (by decide) _,
  separate _ sDom sCtx (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDom (by decide) (by decide) (by decide) _,
  separate _ sDL sDom (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDL (by decide) (by decide) (by decide) _,word_writeW_self,word_writeW_self]
 exact ⟨rfl,rfl,rfl,rfl⟩

theorem entryMemory_range (m : Mem) (B ctx dom dl k : Addr) :
 Outside B 128 32 m (entryMemory m B ctx dom dl k) := by
 intro x hx
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<20) (v : Addr) :
  (m.writeW (off B (8*i)) v) x=m x :=
  writeW_outside m B v (by omega) x (by omega)
 unfold entryMemory
 rw [store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
  store _ sDom (by decide) (by decide),store _ sCtx (by decide) (by decide)]

theorem entryMemory_frame (m : Mem) (B ctx dom dl k : Addr) (Z : Nat) (room : 256≤Z) :
 InScr B Z m (entryMemory m B ctx dom dl k) := by
 have frame := (Frame.refl [⟨B,Z⟩] m).writeW (r:=⟨B,Z⟩) (b:=off B (8*sCtx)) (by simp) ctx
  (Offset.contains_base _ (by unfold sCtx;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDom)) (by simp) dom
  (Offset.contains_base _ (by unfold sDom;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDL)) (by simp) dl
  (Offset.contains_base _ (by unfold sDL;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sLen)) (by simp) k
  (Offset.contains_base _ (by unfold sLen;omega) (by decide))
 intro x hx
 exact frame x (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;subst r;change ¬ofs B x+1≤Z;omega)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataMemory.lean`, which only this module imported.
section

/-! The metadata writer produces exactly the three reviewed header words. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

theorem threeHeaderWords (m : Mem) (a : Addr) (N bytes rows : Nat) :
 Spec.Rsa.wordsAt (((m.writeW (off a 0) (BitVec.ofNat 64 N)).writeW
  (off a 8) (BitVec.ofNat 64 bytes)).writeW (off a 16) (BitVec.ofNat 64 rows)) a 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 bytes,BitVec.ofNat 64 rows] := by
 change [_,_,_]=_
 dsimp only
 rw [List.cons.injEq]
 constructor
 · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
   exact Mem.readW_writeW_self64 _ _ _
 · rw [List.cons.injEq]
   constructor
   · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
     exact Mem.readW_writeW_self64 _ _ _
   · exact congrArg (fun x => [x]) (Mem.readW_writeW_self64 _ _ _)

theorem metadataMemory_header (m : Mem) (B ctx : Addr) (N : Nat) :
 Spec.Rsa.wordsAt (metadataMemory m B ctx N) ctx 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 ((N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)] := by
 simpa only [metadataMemory,off,BitVec.add_zero] using
  threeHeaderWords ((m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
   (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) ctx N ((N+7)/8) (Spec.Rsa.FixedBaseComb.rows N)

theorem metadataMemory_frame (m : Mem) (p : Parameters) (N : Nat) : PublicFrame p m (metadataMemory m p.B p.ctx N) := by
 have bytes := (Frame.refl (publicWrites p) m).writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sBytes)) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sBytes<32 by decide);omega) (by decide))
 have rows := bytes.writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sRows)) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sRows<32 by decide);omega) (by decide))
 have bitHeader := rows.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=p.ctx) (by simp [publicWrites])
  (BitVec.ofNat 64 N) (by change (p.ctx-p.ctx).toNat+8≤8*(3+34*p.w);simp;omega)
 have byteHeader := bitHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 8) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by omega) (by decide))
 exact byteHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 16) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by omega) (by decide))

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataWorkspace.lean`, which only this module imported.
section

/-! Context metadata stores cannot overwrite the separate scratch controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem contextStore_workspace {p : Parameters} {s : State} (space : ContextSpace p s)
 (m : Mem) {d : Nat} (inside : d+8≤8*(3+34*p.w)) (value : Addr) :
 ∀ x,ofs p.B x<p.Z→(m.writeW (off p.ctx d) value) x=m x := by
 intro x hx
 have fit : d+8≤2^64 := by have := p.width;omega
 have outside (i : Nat) (hi : i<8) : p.Z≤ofs p.B (off p.ctx d+BitVec.ofNat 64 i) := by
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using space.outside (d+i) (by omega)
 apply writeW_outside m p.ctx value fit x
 exact (outside_shift_iff p.ctx x (by omega) fit).mpr (le_ofs_of_sep outside hx)

theorem metadataMemory_workspace {p : Parameters} {s : State} (space : ContextSpace p s) (N : Nat) :
 ∀ x,ofs p.B x<p.Z→metadataMemory s.mem p.B p.ctx N x=
 ((s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) x := by
 intro x hx
 unfold metadataMemory
 rw [contextStore_workspace space _ (d:=16) (by omega) _ x hx,
  contextStore_workspace space _ (d:=8) (by omega) _ x hx]
 simpa only [off,BitVec.add_zero] using contextStore_workspace space _ (d:=0) (by omega) _ x hx

theorem metadataMemory_controls {p : Parameters} {s : State} (space : ContextSpace p s)
 (scratch : Scr s p.B p.Z) (N : Nat) :
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8) ∧
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧
 (∀ i<32,i≠sBytes→i≠sRows→word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word s.mem p.B (8*i)) := by
 let m := (s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 have same (i : Nat) (hi : i<32) : word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word m p.B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega) (metadataMemory_workspace space N)
   (by have := hdr_lt_slot p.w 8 hi;have := p.room;omega)
 constructor
 · rw [same sBytes (by decide)]
   exact ((writeW_outside _ _ _ (by decide : 8*sRows+8≤2^64)).word
    (Or.inl (by decide : 8*sBytes+8≤8*sRows)) (by decide)).trans (word_writeW_self _ _ _ _)
 constructor
 · rw [same sRows (by decide)]
   exact word_writeW_self _ _ _ _
 · intro i hi notBytes notRows
   rw [same i hi]
   have separate {j : Nat} (hj : j<32) (different : i≠j) (m : Mem) (v : Addr) :
    word (m.writeW (off p.B (8*j)) v) p.B (8*i)=word m p.B (8*i) :=
    (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)
   exact (separate (by decide) notRows _ _).trans (separate (by decide) notBytes _ _)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PublicSource.lean`, which only this module imported.
section

/-! Checked domain bytes are immutable throughout context creation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PublicSource (p : Parameters) (ptr : Addr) (bs : List Byte) (s : State) : Prop extends Source ptr bs s where
 scratchOutside : ∀ i<bs.length,p.Z≤ofs p.B (ptr+BitVec.ofNat 64 i)
 contextOutside : ∀ i<bs.length,8*(3+34*p.w)≤ofs p.ctx (ptr+BitVec.ofNat 64 i)

theorem PublicSource.after {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (source : PublicSource p ptr bs s) (frame : PublicFrame p s.mem t.mem) (rest : Keep rs s t) : PublicSource p ptr bs t := by
 refine ⟨⟨?_,?_⟩,source.scratchOutside,source.contextOutside⟩
 · intro i hi;rw [rest.rd,rest.wr];exact source.readable i hi
 · intro i hi
   apply Eq.trans (frame _ ?_) (source.bytes i hi)
   intro r hr
   simp only [publicWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · have out := source.scratchOutside i hi
     change ¬ofs p.B (ptr+BitVec.ofNat 64 i)+1≤p.Z
     omega
   · have out := source.contextOutside i hi
     change ¬ofs p.ctx (ptr+BitVec.ofNat 64 i)+1≤8*(3+34*p.w)
     omega

theorem PublicSource.toSrc {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) : Src s p.B p.Z ptr bs := by
 refine ⟨source.readable,?_,source.scratchOutside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

theorem PublicSource.take {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p ptr (bs.take n) s := by
 refine ⟨source.toSource.take n,?_,?_⟩
 all_goals intro i hi;have bound : i<bs.length := by rw [List.length_take] at hi;omega
 · exact source.scratchOutside i bound
 · exact source.contextOutside i bound

theorem PublicSource.drop {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p (ptr+BitVec.ofNat 64 n) (bs.drop n) s := by
 refine ⟨source.toSource.drop n,?_,?_⟩
 all_goals intro i hi;have bound : n+i<bs.length := by rw [List.length_drop] at hi;omega
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.scratchOutside (n+i) bound
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.contextOutside (n+i) bound

theorem PublicSource.generator {p : Parameters} {ptr : Addr} {dom : List Byte} {s : State}
 (source : PublicSource p ptr dom s) (length : 2*p.k≤dom.length)
 (value : p.G=(Spec.Ffdh.domainOf p.k dom).g) :
 GeneratorSource p (ptr+BitVec.ofNat 64 p.k) ((dom.drop p.k).take p.k) s := by
 have bytes := (source.drop p.k).take p.k
 refine ⟨bytes.toSrc,?_,?_,bytes.contextOutside⟩
 · simp only [List.length_take,List.length_drop];omega
 · exact value.symm

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeNative_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom : List Byte} {dl : Nat}
 (scratch : Scr s p.B p.Z) (space : ContextSpace p s) (output : Scr s p.ctx 24)
 (source : PublicSource p domPtr dom s) (span : InRegions (s.rd++s.wr) domPtr p.k)
 (words : p.w=(p.k+7)/8) (small : 64≤p.k) (large : p.k≤1024)
 (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (context : s.gpr .x0=p.ctx) (domain : s.gpr .x2=domPtr) (domainLength : s.gpr .x3=BitVec.ofNat 64 dl)
 (length : s.gpr .x4=BitVec.ofNat 64 p.k) (base : s.gpr .x5=p.B)
 (records : PolicyTableAt p.B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa (Precompute.code M.mm) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 have room : 256≤p.Z := by have := p.room;unfold slot at this;omega
 have positive : 0<p.k := by omega
 have shapeDom : dom.length=2*p.k ∨ dom.length=3*p.k := by omega
 have bits : 0<p.N ∧ p.N≤8192 := by
  rw [policy]
  exact ⟨generation_bits_positive valid,generation_bits_bound positive large⟩
 have facts := (VG.Proof.Ffdh.domainValid_iff p.k dom).mp valid
 have modFacts := facts.1
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modFacts
 unfold Precompute.code
 rw [WP.seq_iff]
 refine WP.mono_syms (precomputeEntry_ok scratch room base) ?_
 rintro a ⟨⟨baseA,memA⟩,restA⟩ symsA
 have entry : a.mem=entryMemory s.mem p.B p.ctx domPtr (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k) := by
  rw [memA,context,domain,domainLength,length]
 have headers := entryMemory_header s.mem p.B p.ctx domPtr (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k)
 rw [←entry] at headers
 have inscrA : InScr p.B p.Z s.mem a.mem := by
  rw [entry];exact entryMemory_frame _ _ _ _ _ _ _ room
 have frameA : PublicFrame p s.mem a.mem := PublicFrame.of_inscr inscrA
 have sourceA := source.after frameA restA
 have recordFrame : Outside p.B 128 32 s.mem a.mem := by rw [entry];exact entryMemory_range _ _ _ _ _ _
 have recordsA : PolicyTableAt p.B (a.syms Policy.tableSym) Policy.groups a := by
  rw [symsA]
  exact records.after_belowBits recordFrame restA (by decide)
 rw [WP.seq_iff]
 refine WP.mono (policyDomain_ok (scratch.congr restA.wr) room baseA positive large shape domLength valid
  headers.2.1 headers.2.2.2 headers.2.2.1 sourceA.toSource
  (fun i hi => Nat.le_trans (by unfold sBits;omega : 8*sBits+8≤p.Z) (source.scratchOutside i hi)) recordsA) ?_
 rintro b ⟨bitsB,frameB,restB⟩
 have inscrB : InScr p.B p.Z a.mem b.mem :=
  InScr.of_outside frameB (by unfold sBits;omega)
 have publicB := PublicFrame.of_inscr (p:=p) inscrB
 have sourceB := sourceA.after publicB restB
 have headersB (i : Nat) (hi : i<32) (different : i≠sBits) : word b.mem p.B (8*i)=word a.mem p.B (8*i) :=
  header_other frameB (by decide) hi different
 rw [WP.seq_iff]
 have before := restA.trans restB
 refine WP.mono (metadata_ok (scratch.congr before.wr) room (output.congr before.wr)
  ((restB.gpr .x0 (by decide)).trans baseA)
  ((headersB sCtx (by decide) (by decide)).trans headers.1)
  (by rw [policy];exact bitsB) bits.1 bits.2) ?_
 rintro c ⟨memC,restC⟩
 have spaceB := space.after before
 have publicC : PublicFrame p b.mem c.mem := by rw [memC];exact metadataMemory_frame _ p _
 have sourceC := sourceB.after publicC restC
 have total := before.trans restC
 have controls := metadataMemory_controls spaceB (scratch.congr before.wr) p.N
 rw [←memC] at controls
 have headerC := metadataMemory_header b.mem p.B p.ctx p.N
 rw [←memC] at headerC
 have sameHeader (i : Nat) (hi : i<32) (different : i≠sBits) (notBytes : i≠sBytes) (notRows : i≠sRows) :
  word c.mem p.B (8*i)=word a.mem p.B (8*i) :=
  (controls.2.2 i hi notBytes notRows).trans (headersB i hi different)
 have odd : p.P%2=1 := by rw [modulus];exact modFacts.1.1.1
 have normalized : 2^(64*(p.w-1))≤p.P := by rw [modulus,words];exact domain_normalized positive valid
 have nbLength : (dom.take p.k).length=p.k := by simp only [List.length_take];omega
 have sourceMod := (sourceC.take p.k).toSrc
 have spanC : InRegions (c.rd++c.wr) domPtr p.k := by rw [total.rd,total.wr];exact span
 refine WP.mono (precomputeArithmetic_ok M (scratch.congr total.wr)
  (((restB.trans restC).gpr .x0 (by simp [recordClobbers])).trans baseA)
  (space.after total) sourceMod spanC nbLength modulus.symm odd normalized
  (sourceC.generator (by omega) generator) words (by omega) (by omega)
  (by rw [generator,modulus];have := facts.2.1;omega) bits
  ((sameHeader sCtx (by decide) (by decide) (by decide) (by decide)).trans headers.1)
  ((sameHeader sDom (by decide) (by decide) (by decide) (by decide)).trans headers.2.1)
  ((sameHeader sLen (by decide) (by decide) (by decide) (by decide)).trans headers.2.2.2)
  controls.2.1 headerC modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,((frameA.trans publicB).trans publicC).trans frameT,
  (total.trans restT).mono (by simp [recordClobbers,mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
