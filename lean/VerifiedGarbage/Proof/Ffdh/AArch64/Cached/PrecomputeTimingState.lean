module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StorePrefix
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFieldFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomain
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Metadata
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataTiming
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognizeTiming
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTailTiming
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognizeTimingState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.TableTiming

/-! ### `Ffdh.AArch64.Cached.PrecomputeNative`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeArithmetic`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeFinish`, which only this module used -/

section

/-! Compose prefix storage and the entire table into a canonical context. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Serialization.lean`, which only this module imported.
section

/-! Native header, Montgomery prefix and table values form the reviewed canonical context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Proof.Bignum

private theorem wordsAt_add (m : Mem) (a : Addr) (n k : Nat) :
 Spec.Rsa.wordsAt m a (n+k)=Spec.Rsa.wordsAt m a n++Spec.Rsa.wordsAt m (off a (8*n)) k := by
 simp only [Spec.Rsa.wordsAt,List.range_add,List.map_append,List.map_map]
 apply congrArg (fun xs => (List.range n).map (fun i => m.readW (a+BitVec.ofNat 64 (8*i)) 64)++xs)
 apply List.map_congr_left
 intro i _
 simp only [Function.comp_apply,off,BitVec.add_assoc,BitVec.ofNat_add,Nat.mul_add]

theorem wordsAt_of_wv {m : Mem} {a : Addr} {d w x : Nat} (value : wv m a d w=x) :
 Spec.Rsa.wordsAt m (off a d) w=Spec.Rsa.toWords x w := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.length_map,List.length_range]
 · intro i hi _
   have bound : i<w := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
   have word := word_eq_ofNat m a d w bound
   rw [value] at word
   simpa only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.getElem_map,List.getElem_range,VG.Proof.Bignum.word,
    off,BitVec.add_assoc,BitVec.ofNat_add] using word

theorem table_words {p : Parameters} {s : State} (table : TablePrefix p 32 s) (n : Nat) (hn : n≤32) :
 Spec.Rsa.wordsAt s.mem (off p.ctx (tableStart p.w)) (n*p.w)=
 (List.range n).flatMap (fun j => Spec.Rsa.toWords (entryValue p j) p.w) := by
 induction n with
 | zero => simp [Spec.Rsa.wordsAt]
 | succ n ih =>
   conv_lhs => arg 3;rw [Nat.add_mul,Nat.one_mul]
   rw [wordsAt_add,ih (by omega_using [hn]),List.range_succ,List.flatMap_append]
   simp only [List.flatMap_singleton]
   congr 1
   have addr : off (off p.ctx (tableStart p.w)) (8*(n*p.w))=off p.ctx (entryOffset p.w n) := by
    unfold off
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    unfold tableStart entryOffset
    ring
   rw [addr]
   exact wordsAt_of_wv (table n (by omega_using [hn]))

theorem canonical_words {p : Parameters} {s : State} {dom : List Byte}
 (words : p.w=Spec.Rsa.modulusWords p.k) (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p)
 (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g) (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (first : wv s.mem p.ctx 24 p.w=p.P) (second : wv s.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P)
 (table : TablePrefix p 32 s) :
 Spec.Rsa.wordsAt s.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom := by
 have length : Spec.Ffdh.generationPrecomputedWords p.k=3+(2*p.w+32*p.w) := by
  simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
   Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,←words]
 rw [length,wordsAt_add]
 change Spec.Rsa.wordsAt s.mem p.ctx 3++Spec.Rsa.wordsAt s.mem (off p.ctx 24) (2*p.w+32*p.w)=_
 rw [wordsAt_add,header]
 have addr : off (off p.ctx 24) (8*(2*p.w))=off p.ctx (tableStart p.w) := by
  unfold off tableStart
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  omega_using []
 rw [addr,table_words table 32 (by omega_using [])]
 have mont : Spec.Rsa.wordsAt s.mem (off p.ctx 24) (2*p.w)=
   Spec.Rsa.toWords p.P p.w++Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w := by
  rw [show 2*p.w=p.w+p.w by omega_using [],wordsAt_add,wordsAt_of_wv first]
  have addr2 : off (off p.ctx 24) (8*p.w)=off p.ctx (24+8*p.w) := by
   simp only [off,BitVec.add_assoc,BitVec.ofNat_add]
  rw [addr2,wordsAt_of_wv second]
 rw [mont]
 simp only [VG.Proof.Ffdh.generationValues,Spec.Rsa.FixedBaseComb.table,Spec.Rsa.FixedBaseComb.entries,
  Spec.Rsa.FixedBaseComb.teeth,entryValue,words,modulus,generator,policy,List.append_assoc]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem prefixWords_unchanged {p : Parameters} {s t : State} {n : Nat}
 (_space : ContextSpace p s) (same : ∀ i<8*n,t.mem (p.ctx+BitVec.ofNat 64 i)=s.mem (p.ctx+BitVec.ofNat 64 i)) :
 Spec.Rsa.wordsAt t.mem p.ctx n=Spec.Rsa.wordsAt s.mem p.ctx n := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
 · intro i hi _
   have index : i<n := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
   apply Mem.readW_congr
   intro b hb
   simpa only [BitVec.ofNat_add,BitVec.add_assoc] using same (8*i+b) (by omega_using [index, hb])

theorem precomputeFinish_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (source : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) bs s)
 (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=domPtr)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)) :
 WP isa (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1]))) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 rw [WP.seq_iff]
 refine WP.mono (storePrefix_ok field space context) ?_
 rintro a ⟨fieldA,firstA,secondA,frameA,sameA,restA⟩
 have spaceA := space.after restA
 have headerA : Spec.Rsa.wordsAt a.mem p.ctx 3=Spec.Rsa.wordsAt s.mem p.ctx 3 := by
  apply prefixWords_unchanged space
  intro i hi
  exact frameA _ (Or.inl (by rw [show ofs p.ctx (p.ctx+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [hi])];omega_using [hi]))
 have sourceA : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) bs a := by
  refine ⟨⟨?_,?_,source.source.out⟩,source.length,source.value,source.separate⟩
  · intro i hi;rw [restA.rd,restA.wr];exact source.source.rd i hi
  · intro i hi
    exact (frameA _ (Or.inr (by have := source.separate i hi;omega_using [this]))).trans (source.source.val i hi)
 have sameHeader (i : Nat) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) :=
  workspace_header field.good sameA hi
 rw [WP.seq_iff]
 refine WP.mono (precomputeTable_ok M fieldA spaceA sourceA words positive size reduced bits
  ((sameHeader sCtx (by decide)).trans context) ((sameHeader sDom (by decide)).trans domain)
  ((sameHeader sLen (by decide)).trans length) ((sameHeader sRows (by decide)).trans rows)) ?_
 rintro b ⟨basisB,frameB,restB⟩
 have canonical : Spec.Rsa.wordsAt b.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom := by
  apply canonical_words (by simpa only [Spec.Rsa.modulusWords] using words) modulus generator policy
  · rw [prefixWords_unchanged spaceA (fun i hi => frameB.prefix spaceA (by unfold tableStart;omega_using [hi])),headerA,header]
  · apply Eq.trans _ firstA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    have same := frameB.prefix spaceA (i:=24+8*i+j) (by unfold tableStart;omega_using [hi, hj])
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · apply Eq.trans _ secondA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    have same := frameB.prefix spaceA (i:=24+8*p.w+8*i+j) (by unfold tableStart;omega_using [hi, hj])
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · exact basisB.table
 refine WP.mono (WP.keep [.x0] (Q:=fun t =>t.gpr .x0=1#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun
 · rintro t ⟨⟨status,mem⟩,rest⟩
   exact ⟨status,by rw [mem];exact canonical,
    by rw [mem];exact (PublicFrame.of_context frameA (by omega_using [])).trans (PublicFrame.of_build frameB),
    ((restA.trans restB).trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! All arithmetic after public metadata: modulus loading, R², prefix and table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeArithmetic_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom nb gb : List Byte}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (space : ContextSpace p s)
 (modulusSource : Src s p.B p.Z domPtr nb) (modulusSpan : InRegions (s.rd++s.wr) domPtr p.k)
 (nbLength : nb.length=p.k) (nbValue : Spec.Rsa.os2ip nb=p.P)
 (odd : p.P%2=1) (normalized : 2^(64*(p.w-1))≤p.P)
 (source : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) gb s)
 (words : p.w=(p.k+7)/8) (positive : 9≤p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=domPtr)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)) :
 WP isa (.seq (seqs (pcLoadW++r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 rw [WP.seq_iff]
 have room : slot ((p.k+7)/8) 8≤p.Z := by rw [←words];exact p.room
 refine WP.mono (precomputeField_ok M scratch base room positive size length domain modulusSource modulusSpan nbLength
  (by rw [nbValue];exact odd) (by rw [nbValue,←words];exact normalized)) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 have fieldA : FieldInitial q a := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [q,words] using goodA
  · simpa only [q,words,nbValue] using modulusA
  · simpa only [q,words] using inverseA
  · simpa only [q,words,nbValue] using r2A
 have inscr : InScr p.B p.Z s.mem a.mem := by
  apply precomputeField_inscr (w:=p.w) _ p.room
  simpa only [words] using frameA
 have frame (i : Nat) (hi : 16≤i) (hi' : i<32) (counter : i≠Public.sCnt) :
  word a.mem p.B (8*i)=word s.mem p.B (8*i) := precomputeField_header frameA hi hi' counter
 have spaceA : ContextSpace q a := ⟨(space.after restA).writable,space.outside⟩
 have sourceAP := source.after_inscr inscr restA
 have sourceA : GeneratorSource q (domPtr+BitVec.ofNat 64 q.k) gb a :=
  ⟨sourceAP.source,source.length,source.value,source.separate⟩
 have headerA : Spec.Rsa.wordsAt a.mem p.ctx 3=Spec.Rsa.wordsAt s.mem p.ctx 3 := by
  apply prefixWords_unchanged (n:=3) space
  intro i hi
  exact inscr _ (space.outside i (by omega_using [hi]))
 refine WP.mono (precomputeFinish_ok M fieldA spaceA sourceA words (by change 0<p.k;omega_using [positive]) size reduced bits
  ((frame sCtx (by decide) (by decide) (by decide)).trans context)
  ((frame sDom (by decide) (by decide) (by decide)).trans domain)
  ((frame sLen (by decide) (by decide) (by decide)).trans length)
  ((frame sRows (by decide) (by decide) (by decide)).trans rows)
  (headerA.trans header) modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,(PublicFrame.of_inscr inscr).trans frameT,
  (restA.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

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
  scratch.st (d:=8*sCtx) (by unfold sCtx;omega_using [room]),
  scratch.st (d:=8*sDom) (by unfold sDom;omega_using [room]),
  scratch.st (d:=8*sDL) (by unfold sDL;omega_using [room]),
  scratch.st (d:=8*sLen) (by unfold sLen;omega_using [room])]

theorem entryMemory_header (m : Mem) (B ctx dom dl k : Addr) :
 word (entryMemory m B ctx dom dl k) B (8*sCtx)=ctx ∧
 word (entryMemory m B ctx dom dl k) B (8*sDom)=dom ∧
 word (entryMemory m B ctx dom dl k) B (8*sDL)=dl ∧
 word (entryMemory m B ctx dom dl k) B (8*sLen)=k := by
 have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
  word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
  Mem.readW_writeW_sep (Offset.sep B (by omega_using [different]) (by omega_using [hj]) (by omega_using [hi])) (by decide)
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
  writeW_outside m B v (by omega_using [high]) x (by omega_using [hx, low, high])
 unfold entryMemory
 rw [store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
  store _ sDom (by decide) (by decide),store _ sCtx (by decide) (by decide)]

theorem entryMemory_frame (m : Mem) (B ctx dom dl k : Addr) (Z : Nat) (room : 256≤Z) :
 InScr B Z m (entryMemory m B ctx dom dl k) := by
 have frame := (Frame.refl [⟨B,Z⟩] m).writeW (r:=⟨B,Z⟩) (b:=off B (8*sCtx)) (by simp) ctx
  (Offset.contains_base _ (by unfold sCtx;omega_using [room]) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDom)) (by simp) dom
  (Offset.contains_base _ (by unfold sDom;omega_using [room]) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDL)) (by simp) dl
  (Offset.contains_base _ (by unfold sDL;omega_using [room]) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sLen)) (by simp) k
  (Offset.contains_base _ (by unfold sLen;omega_using [room]) (by decide))
 intro x hx
 exact frame x (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;subst r;change ¬ofs B x+1≤Z;omega_using [hx])

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
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sBytes<32 by decide);omega_arith) (by decide))
 have rows := bytes.writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sRows)) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sRows<32 by decide);omega_arith) (by decide))
 have bitHeader := rows.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=p.ctx) (by simp [publicWrites])
  (BitVec.ofNat 64 N) (by change (p.ctx-p.ctx).toNat+8≤8*(3+34*p.w);simp;omega_using [])
 have byteHeader := bitHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 8) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by omega_using []) (by decide))
 exact byteHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 16) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by omega_using []) (by decide))

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
 have fit : d+8≤2^64 := by have := p.width;omega_using [inside, this]
 have outside (i : Nat) (hi : i<8) : p.Z≤ofs p.B (off p.ctx d+BitVec.ofNat 64 i) := by
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using space.outside (d+i) (by omega_using [inside, hi])
 apply writeW_outside m p.ctx value fit x
 exact (outside_shift_iff p.ctx x (by omega_using [fit]) fit).mpr (le_ofs_of_sep outside hx)

theorem metadataMemory_workspace {p : Parameters} {s : State} (space : ContextSpace p s) (N : Nat) :
 ∀ x,ofs p.B x<p.Z→metadataMemory s.mem p.B p.ctx N x=
 ((s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) x := by
 intro x hx
 unfold metadataMemory
 rw [contextStore_workspace space _ (d:=16) (by omega_using []) _ x hx,
  contextStore_workspace space _ (d:=8) (by omega_using []) _ x hx]
 simpa only [off,BitVec.add_zero] using contextStore_workspace space _ (d:=0) (by omega_using []) _ x hx

theorem metadataMemory_controls {p : Parameters} {s : State} (space : ContextSpace p s)
 (scratch : Scr s p.B p.Z) (N : Nat) :
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8) ∧
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧
 (∀ i<32,i≠sBytes→i≠sRows→word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word s.mem p.B (8*i)) := by
 let m := (s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 have same (i : Nat) (hi : i<32) : word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word m p.B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega_using [this]) (metadataMemory_workspace space N)
   (by have := hdr_lt_slot p.w 8 hi;have := p.room;omega_arith)
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
    (writeW_outside _ _ _ (by omega_using [hj])).word (by omega_using [different]) (by omega_using [hi])
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
     omega_using [out]
   · have out := source.contextOutside i hi
     change ¬ofs p.ctx (ptr+BitVec.ofNat 64 i)+1≤8*(3+34*p.w)
     omega_using [out]

theorem PublicSource.toSrc {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) : Src s p.B p.Z ptr bs := by
 refine ⟨source.readable,?_,source.scratchOutside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

theorem PublicSource.take {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p ptr (bs.take n) s := by
 refine ⟨source.toSource.take n,?_,?_⟩
 all_goals intro i hi;have bound : i<bs.length := by rw [List.length_take] at hi;omega_using [hi]
 · exact source.scratchOutside i bound
 · exact source.contextOutside i bound

theorem PublicSource.drop {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p (ptr+BitVec.ofNat 64 n) (bs.drop n) s := by
 refine ⟨source.toSource.drop n,?_,?_⟩
 all_goals intro i hi;have bound : n+i<bs.length := by rw [List.length_drop] at hi;omega_using [hi]
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.scratchOutside (n+i) bound
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.contextOutside (n+i) bound

theorem PublicSource.generator {p : Parameters} {ptr : Addr} {dom : List Byte} {s : State}
 (source : PublicSource p ptr dom s) (length : 2*p.k≤dom.length)
 (value : p.G=(Spec.Ffdh.domainOf p.k dom).g) :
 GeneratorSource p (ptr+BitVec.ofNat 64 p.k) ((dom.drop p.k).take p.k) s := by
 have bytes := (source.drop p.k).take p.k
 refine ⟨bytes.toSrc,?_,?_,bytes.contextOutside⟩
 · simp only [List.length_take,List.length_drop];omega_using [length]
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
 have room : 256≤p.Z := by have := p.room;unfold slot at this;omega_using [words, small, this]
 have positive : 0<p.k := by omega_using [small]
 have shapeDom : dom.length=2*p.k ∨ dom.length=3*p.k := by omega_using [shape, domLength]
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
  (fun i hi => Nat.le_trans (by unfold sBits;omega_using [room] : 8*sBits+8≤p.Z) (source.scratchOutside i hi)) recordsA) ?_
 rintro b ⟨bitsB,frameB,restB⟩
 have inscrB : InScr p.B p.Z a.mem b.mem :=
  InScr.of_outside frameB (by unfold sBits;omega_using [room])
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
 have nbLength : (dom.take p.k).length=p.k := by simp only [List.length_take];omega_using [shape, domLength]
 have sourceMod := (sourceC.take p.k).toSrc
 have spanC : InRegions (c.rd++c.wr) domPtr p.k := by rw [total.rd,total.wr];exact span
 refine WP.mono (precomputeArithmetic_ok M (scratch.congr total.wr)
  (((restB.trans restC).gpr .x0 (by simp [recordClobbers])).trans baseA)
  (space.after total) sourceMod spanC nbLength modulus.symm odd normalized
  (sourceC.generator (by omega_using [shape, domLength]) generator) words (by omega_using [small]) (by omega_using [large])
  (by rw [generator,modulus];have := facts.2.1;omega_using [this]) bits
  ((sameHeader sCtx (by decide) (by decide) (by decide) (by decide)).trans headers.1)
  ((sameHeader sDom (by decide) (by decide) (by decide) (by decide)).trans headers.2.1)
  ((sameHeader sLen (by decide) (by decide) (by decide) (by decide)).trans headers.2.2.2)
  controls.2.1 headerC modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,((frameA.trans publicB).trans publicC).trans frameT,
  (total.trans restT).mono (by simp [recordClobbers,mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Public inputs and staging predicates for the complete context initializer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyDomainTiming.lean`, which only this module imported.
section

/-! Checked public domains discharge all leading-zero and recognition timing premises. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh (lead)
open VG.Proof.Ffdh.KeyScalar (bnd)

structure DomainPolicyPublic where
 B : Addr
 Z : Nat
 src : Addr
 dom : List Byte
 k : Nat
 dl : Nat
 table : Addr
 room : 256≤Z
 positive : 0<k
 size : k≤1024
 shape : dl=2*k ∨ dl=3*k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid k dom=true

structure DomainPolicyReady (q : DomainPolicyPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 pointer : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k
 domainLength : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dl
 source : Source q.src q.dom s
 outside : ∀ i<q.dom.length,8*sBits+8≤ofs q.B (q.src+BitVec.ofNat 64 i)
 records : PolicyTableAt q.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

def domainRecognize (q : DomainPolicyPublic) : RecognizePublic := by
 have shape : q.dom.length=2*q.k ∨ q.dom.length=3*q.k :=by have :=q.domLength;have :=q.shape;omega_arith
 have leadFacts:=checked_bound_lead q.positive shape q.checked
 exact {
  B:=q.B,Z:=q.Z,dom:=q.src,k:=q.k,dl:=q.dl,bs:=bnd q.k q.dom,L:=lead (bnd q.k q.dom),room:=q.room,
  positive:=q.positive,size:=by have :=q.size;omega_using [this],shape:=q.shape,length:=VG.Proof.Ffdh.KeyScalar.bnd_length shape,
  inside:=leadFacts.1,zeros:=leadFacts.2.1,nonzero:=leadFacts.2.2,
  domBytes:=q.dom,table:=q.table,domLength:=q.domLength,small:=by have :=q.size;omega_using [this]}

theorem domainRecognize_ready {q : DomainPolicyPublic} {s : State} (h : DomainPolicyReady q s) :
 RecognizeReady (domainRecognize q) s := by
 refine ⟨⟨h.scratch,h.base,h.pointer,h.length,h.domainLength,?_⟩,h.source,h.outside,h.records,h.symbol⟩
 change Source (if q.dl=2*q.k then q.src else off q.src (2*q.k)) (bnd q.k q.dom) s
 exact h.source.bound q.positive q.domLength q.shape

theorem policyDomain_ct : RelCT isa (Two DomainPolicyReady) Policy.recognize (fun _ _ =>True) :=
 two_map domainRecognize (fun _ _ h =>domainRecognize_ready h) policyRecognize_ct

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeFieldTiming.lean`, which only this module imported.
section

/-! Reuse the existing public modulus-load and R-squared timing proofs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeField_ct (M : Mont) : RelCT isa (Two PcM)
 (VG.Impl.Bignum.AArch64.seqs (pcLoadW++r2StepsPub M.mm)) (fun _ _ =>True) := by
 refine RelCT.seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) (RelCT.seq
  (two_post (Ψ:=Pc3) (pcLoadW_ct.mono (fun _ _ h =>two_mono (fun _ _ h =>PcM.loadW h) h) (fun _ _ _ =>trivial)) ?_)
  ((pcR2_ct M).mono (fun _ _ h =>h) (fun _ _ _ =>trivial)))
 intro p s h
 have h':=h
 obtain ⟨scratch,base,room,small,large,_,length,modulus,source,nbLength,valid,_,_,span⟩:=h'
 exact WP.mono (pcLoadW_r2 scratch base room small large length modulus source span nbLength valid)
  (fun t ⟨mi,r2,frame,rest⟩ =>⟨mi,h.congr frame (fun r hr =>Nat.le_trans (pcLoadRanges_le _ r hr) room)
   (pcLoadRanges_fixed _) rest (by decide),r2⟩)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTimingState.lean`, which only this module imported.
section

/-! Public modulus setup establishes the table builder's field without assuming prior scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ArithmeticPublic where
 table : TablePublic
 nb : List Byte
 value : Spec.Rsa.os2ip nb=table.p.P
 odd : table.p.P%2=1

def arithmeticPc (q : ArithmeticPublic) : PcPub :=
 ⟨q.table.p.B,q.table.p.Z,q.table.p.k,q.table.p.ctx,q.table.dom,q.nb⟩

def arithmeticTable (q : ArithmeticPublic) (mi : BitVec 64) : TablePublic :=
 {q.table with p:={q.table.p with mi:=mi}}

structure ArithmeticReady (q : ArithmeticPublic) (s : State) : Prop where
 pc : PcM (arithmeticPc q) s
 space : ContextSpace q.table.p s
 generator : GeneratorSource q.table.p (q.table.dom+BitVec.ofNat 64 q.table.p.k) q.table.bs s
 rows : word s.mem q.table.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.table.p.N)

def ArithmeticDone (q : ArithmeticPublic) (s : State) : Prop :=∃ mi,TableReady (arithmeticTable q mi) s

theorem arithmeticField_done (M : Mont) {q : ArithmeticPublic} {s : State} (h : ArithmeticReady q s) :
 WP isa (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm)) s (ArithmeticDone q) := by
 obtain ⟨scratch,base,room,small,large,ctx,len,dom,source,nbLength,valid,_,_,span⟩:=h.pc
 dsimp only [arithmeticPc,PcPub.w,PcPub.N] at *
 have normalized :=(valid_facts valid small).2.2
 refine WP.mono (precomputeField_ok M scratch base room (by change 9≤q.table.p.k;change 64≤q.table.p.k at small;omega_using [small])
  q.table.size len dom source span nbLength (by rw [q.value];exact q.odd) normalized) ?_
 rintro t ⟨mi,good,modulus,inverse,r2,frame,rest⟩
 have field : FieldInitial (arithmeticTable q mi).p t :=by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [arithmeticTable,q.table.words] using good
  · simpa only [arithmeticTable,q.table.words,q.value] using modulus
  · simpa only [arithmeticTable,q.table.words] using inverse
  · simpa only [arithmeticTable,q.table.words,q.value] using r2
 have inscr : InScr q.table.p.B q.table.p.Z s.mem t.mem :=by
  apply precomputeField_inscr (w:=q.table.p.w) _ q.table.p.room
  simpa only [q.table.words] using frame
 have sourceT:=h.generator.after_inscr inscr rest
 have header (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠Public.sCnt) :=precomputeField_header frame lo hi different
 exact ⟨mi,⟨field,⟨(h.space.after rest).writable,h.space.outside⟩,
  ⟨sourceT.source,sourceT.length,sourceT.value,sourceT.separate⟩,
  (header sCtx (by decide) (by decide) (by decide)).trans ctx,
  (header sDom (by decide) (by decide) (by decide)).trans dom,
  (header sLen (by decide) (by decide) (by decide)).trans len⟩,
  (header sRows (by decide) (by decide) (by decide)).trans h.rows⟩

theorem arithmeticDone_two {s t : State} (h : Two ArithmeticDone s t) : Two TableReady s t := by
 obtain ⟨q,⟨a,hs⟩,⟨b,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.table.p) hs.field ht.field q.odd
 subst b
 exact ⟨arithmeticTable q a,hs,ht,sp⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTiming.lean`, which only this module imported.
section

/-! Compose public field setup with context serialization and the complete fixed-base table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeArithmetic_ct (M : Mont) : RelCT isa (Two ArithmeticReady)
 (.seq (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) (fun _ _ =>True) :=
 RelCT.seq (two_post (two_map arithmeticPc (fun _ _ h =>h.pc) (precomputeField_ct M))
  (fun _ _ h =>arithmeticField_done M h))
  ((precomputeTail_ct M).mono (fun _ _ h =>arithmeticDone_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PrecomputePublic where
 p : Parameters
 domPtr : Addr
 dom : List Byte
 dl : Nat
 table : Addr
 words : p.w=(p.k+7)/8
 small : 64≤p.k
 large : p.k≤1024
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid p.k dom=true
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 generator : p.G=(Spec.Ffdh.domainOf p.k dom).g
 policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)

theorem precomputeBits (q : PrecomputePublic) : 0<q.p.N ∧ q.p.N≤8192 :=by
 rw [q.policy]
 exact ⟨generation_bits_positive q.checked,generation_bits_bound (by have :=q.small;omega_using [this]) q.large⟩

def precomputeDomainPolicy (q : PrecomputePublic) : DomainPolicyPublic :=
 ⟨q.p.B,q.p.Z,q.domPtr,q.dom,q.p.k,q.dl,q.table,
  by have :=q.p.room;dsimp only [slot,hdrBytes] at this;omega_using [this],by have :=q.small;omega_using [this],q.large,q.shape,q.domLength,q.checked⟩

def precomputeMetadata (q : PrecomputePublic) : MetadataPublic :=
 ⟨q.p.B,q.p.Z,q.p.ctx,q.p.N,(precomputeDomainPolicy q).room,(precomputeBits q).1,(precomputeBits q).2⟩

def precomputeArithmetic (q : PrecomputePublic) : ArithmeticPublic :=by
 have facts :=(VG.Proof.Ffdh.domainValid_iff q.p.k q.dom).mp q.checked
 have reduced : q.p.G<q.p.P :=by rw [q.generator,q.modulus];have :=facts.2.1;omega_using [this]
 have odd : q.p.P%2=1 :=by
  have mod:=VG.Proof.Ffdh.domainValid_mod q.checked
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
  rw [q.modulus];exact mod.1.1.1
 exact ⟨⟨⟨q.p,q.domPtr,(q.dom.drop q.p.k).take q.p.k,q.words,by have :=q.small;omega_using [this],
  by have :=q.large;omega_using [this],reduced⟩,precomputeBits q⟩,q.dom.take q.p.k,q.modulus.symm,odd⟩

structure PrecomputeReady (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 context : s.gpr .x0=q.p.ctx
 domain : s.gpr .x2=q.domPtr
 domainLength : s.gpr .x3=BitVec.ofNat 64 q.dl
 length : s.gpr .x4=BitVec.ofNat 64 q.p.k
 base : s.gpr .x5=q.p.B
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputeSetup (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 base : s.gpr .x0=q.p.B
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.domPtr
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

structure PrecomputeEntered (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputePolicyDone (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 bits : word s.mem q.p.B (8*sBits)=BitVec.ofNat 64 q.p.N

theorem precomputeEntered_policy {q : PrecomputePublic} {s : State} (h : PrecomputeEntered q s) :
 DomainPolicyReady (precomputeDomainPolicy q) s :=
 ⟨h.scratch,h.base,h.domain,h.length,h.domainLength,h.source.toSource,
  fun i hi =>Nat.le_trans (by have :=q.p.room;dsimp only [slot,hdrBytes,sBits] at *;omega_using [this]) (h.source.scratchOutside i hi),h.records,h.symbol⟩

theorem precomputePolicyDone_metadata {q : PrecomputePublic} {s : State} (h : PrecomputePolicyDone q s) :
 MetadataReady (precomputeMetadata q) s :=⟨h.scratch,h.base,h.context,h.bits⟩

end VG.Proof.Ffdh.AArch64.Cached
