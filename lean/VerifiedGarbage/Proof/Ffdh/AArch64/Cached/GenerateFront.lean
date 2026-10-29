module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextView
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Context
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Sample
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
/-! Connect immutable context import and policy sampling to the comb's initial state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ContextPrefix.lean`, which only this module imported.
section

/-! The canonical context contains exact, unreduced-width p and reduced R² limbs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_prefix {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 wv m ctx 24 w=P ∧ wv m ctx (24+8*w) w=2^(128*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 have countEq : count=3+34*w := context_words_count canonical
 have bound : P<2^(64*w) := by
  have h := os2ip_lt (dom.take k)
  have len : (dom.take k).length=k := by simp only [List.length_take];omega
  rw [len,pow256_eq] at h
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega))
 have positive : 0<P := by
  have h := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega
 have prefixWords : Spec.Rsa.wordsAt m (off ctx 24) (2*w)=Spec.Rsa.toWords P w++Spec.Rsa.toWords (2^(128*w)%P) w := by
  have slice := VG.Proof.Mont.wordsAt_slice m ctx 0 count 3 (2*w) (by omega)
  have src := context_words length valid canonical
  simp only [VG.Proof.Mont.off,BitVec.add_zero,Nat.zero_add] at slice
  rw [src] at slice
  rw [VG.Proof.Ffdh.generationValues_montgomery] at slice
  exact slice.symm
 have values := pre_words prefixWords bound (Nat.lt_trans (Nat.mod_lt _ positive) bound)
 have zero : wv m (off ctx 24) 0 w=wv m ctx 24 w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.zero_add]
 have second : wv m (off ctx 24) (8*w) w=wv m ctx (24+8*w) w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.add_assoc]
 exact ⟨zero.symm.trans values.1,second.symm.trans values.2⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleFrame.lean`, which only this module imported.
section

/-! Sampling modifies the private output and its dedicated mask control only. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem sampleFrame_header {p : Parameters} {s t : State} {N i : Nat}
 (scratch : Scr s p.B p.Z) (inside : i<32) (different : i≠sMask)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 word t.mem p.B (8*i)=word s.mem p.B (8*i) := by
 rw [workspace_word (by have := scratch.nowrap;omega) same
  (by have := hdr_lt_slot p.w 8 inside;have := p.room;omega)]
 exact header_other (writeW_outside _ _ _ (by decide : 8*sMask+8≤2^64)) (by decide) inside different

theorem FieldInitial.after_sample {p : Parameters} {s t : State} {N : Nat}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) : FieldInitial p t := by
 have nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega
 have masked := writeW_outside s.mem p.B (sampleMask N) (by decide : 8*sMask+8≤2^64)
 have arrays (a : Nat) (ha : a<8) : wv t.mem p.B (slot p.w a) p.w=wv s.mem p.B (slot p.w a) p.w := by
  have within := Nat.le_trans (slot_le (w:=p.w) ha) p.room
  apply Eq.trans _ (masked.wv (Or.inr (hdr_lt_slot p.w a (show sMask<32 by decide))) (by have := slot_le (w:=p.w) ha;omega))
  apply wv_congr
  intro i hi
  exact workspace_word (by have := field.good.scr.nowrap;omega) same (by omega)
 have wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  rw [workspace_word (by have := field.good.scr.nowrap;omega) same
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.room;have := p.positive;omega)]
  exact masked.word (Or.inr (hdr_lt_slot p.w 0 (show sMask<32 by decide)))
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.positive;omega)
 refine ⟨good,(arrays 0 (by decide)).trans field.modulus,?_,(arrays 4 (by decide)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_sample {p : Parameters} {s t : State} {N k : Nat}
 (h : Controls p.B p.src p.ctx k p.N s) (scratch : Scr s p.B p.Z)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 Controls p.B p.src p.ctx k p.N t :=
 ⟨(sampleFrame_header scratch (by decide) (by decide) same).trans h.context,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.source,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.length,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.bits,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generateFront_ok {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (controls : Controls p.B p.src p.ctx p.k p.N s)
 (domain : word s.mem p.B (8*sDom)=dp) (domLen : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (y : word s.mem p.B (8*sY)=yp) (rand : word s.mem p.B (8*sRand)=rp)
 (bytes : word s.mem p.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8))
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i)) :
 WP isa (.seq importPrefix Generate.sample) s fun t =>
 ∃ mi,let q : Parameters := {p with mi:=mi}
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 Initial q bs t ∧ Spec.Rsa.os2ip bs=Spec.Rsa.os2ip rb%2^p.N ∧
 Src t p.B p.Z dp dom ∧ word t.mem p.B (8*sDom)=dp ∧
 word t.mem p.B (8*sDL)=BitVec.ofNat 64 dl ∧ word t.mem p.B (8*sY)=yp ∧ Keep mmRegs s t := by
 have domSize : p.k≤dom.length := by omega
 have validMod := VG.Proof.Ffdh.domainValid_mod valid
 have prefixValues := context_prefix domSize validMod view.canonical
 have wEq : p.w=Spec.Rsa.modulusWords p.k := words
 rw [←wEq,←modulus] at prefixValues
 have countEq : count=3+34*p.w := by rw [context_words_count view.canonical,←wEq]
 have odd : p.P%2=1 := by
  have h := validMod
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  rw [modulus];exact h.1.1.1
 rw [WP.seq_iff]
 refine WP.mono (importPrefix_ok scratch base p.room words positive size controls.length controls.context
  (fun i hi =>by
   have h := view.readable (3+i) (by omega)
   simpa only [off,Nat.mul_add] using h)
  (fun i hi =>by
   have h := view.outside (24+i) (by omega)
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using h)
  prefixValues.1 prefixValues.2 odd) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 have fieldA : FieldInitial q a := ⟨goodA,modulusA,inverseA,r2A⟩
 have inscrA : InScr p.B p.Z s.mem a.mem := InScr.of_frm frameA
  (fun r hr =>Nat.le_trans (importRanges_le _ r hr) p.room)
 have viewA := view.after_inscr inscrA restA
 have domainA := domainSource.congrK inscrA restA
 have randomA := randomSource.congrK inscrA restA
 have headerA (i : Nat) (lo : 16≤i) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) := importFrame_header frameA lo hi
 have controlsA : Controls q.B q.src q.ctx q.k q.N a :=
  ⟨(headerA sCtx (by decide) (by decide)).trans controls.context,
   (headerA sX (by decide) (by decide)).trans controls.source,
   (headerA sLen (by decide) (by decide)).trans controls.length,
   (headerA sBits (by decide) (by decide)).trans controls.bits,
   (headerA sRows (by decide) (by decide)).trans controls.rows⟩
 refine WP.mono (sample_ok goodA p.room positive size bitsPositive bitsBound width rbLength controlsA.bits
  ((headerA sBytes (by decide) (by decide)).trans bytes) controlsA.length controlsA.source
  ((headerA sRand (by decide) (by decide)).trans rand) randomA
  (fun i hi =>by rw [restA.wr];exact writeX i hi) outsideX separateRand) ?_
 rintro t ⟨goodT,_,valueT,sameT,frameT,restT⟩
 have total : Keep mmRegs s t := (restA.trans restT).mono (by simp [mmRegs])
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 have bsLength : bs.length=p.k := by simp only [bs,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 have fieldT := fieldA.after_sample goodT sameT
 have controlsT := controlsA.after_sample goodA.scr sameT
 have viewT := viewA.after_output frameT restT separateContext
 have domainT := src_after_output domainA frameT restT separateDomain
 have actual : Source q.src bs t := source_of_bytesAt t p.src p.k (fun i hi =>by
  obtain ⟨r,hr,contains⟩ := writeX i hi
  exact ⟨r,List.mem_append_right _ (by rw [total.wr];exact hr),contains⟩)
 have readsT : ReadEnv q bs t := context_readEnv wEq modulus generator policy table domSize validMod viewT.canonical
  actual bsLength (fun i hi =>outsideX i (by omega)) viewT.readable viewT.outside
 have headerT (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠sMask) : word t.mem p.B (8*i)=word s.mem p.B (8*i) :=
  (sampleFrame_header (p:=q) goodA.scr hi different sameT).trans (headerA i lo hi)
 refine ⟨mi,⟨fieldT,?_,readsT⟩,valueT,domainT,?_,?_,?_,total⟩
 · change Controls q.B q.src q.ctx bs.length q.N t
   rw [bsLength]
   exact controlsT
 · exact (headerT sDom (by decide) (by decide) (by decide)).trans domain
 · exact (headerT sDL (by decide) (by decide) (by decide)).trans domLen
 · exact (headerT sY (by decide) (by decide) (by decide)).trans y

end VG.Proof.Ffdh.AArch64.Cached
