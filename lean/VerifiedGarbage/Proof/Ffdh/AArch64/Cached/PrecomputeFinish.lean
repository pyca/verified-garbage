module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StorePrefix
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Serialization
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose prefix storage and the entire table into a canonical context. -/
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
   simpa only [BitVec.ofNat_add,BitVec.add_assoc] using same (8*i+b) (by omega)

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
  exact frameA _ (Or.inl (by rw [show ofs p.ctx (p.ctx+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega)];omega))
 have sourceA : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) bs a := by
  refine ⟨⟨?_,?_,source.source.out⟩,source.length,source.value,source.separate⟩
  · intro i hi;rw [restA.rd,restA.wr];exact source.source.rd i hi
  · intro i hi
    exact (frameA _ (Or.inr (by have := source.separate i hi;omega))).trans (source.source.val i hi)
 have sameHeader (i : Nat) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) :=
  workspace_header field.good sameA hi
 rw [WP.seq_iff]
 refine WP.mono (precomputeTable_ok M fieldA spaceA sourceA words positive size reduced bits
  ((sameHeader sCtx (by decide)).trans context) ((sameHeader sDom (by decide)).trans domain)
  ((sameHeader sLen (by decide)).trans length) ((sameHeader sRows (by decide)).trans rows)) ?_
 rintro b ⟨basisB,frameB,restB⟩
 have canonical : Spec.Rsa.wordsAt b.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom := by
  apply canonical_words (by simpa only [Spec.Rsa.modulusWords] using words) modulus generator policy
  · rw [prefixWords_unchanged spaceA (fun i hi => frameB.prefix spaceA (by unfold tableStart;omega)),headerA,header]
  · apply Eq.trans _ firstA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    have same := frameB.prefix spaceA (i:=24+8*i+j) (by unfold tableStart;omega)
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · apply Eq.trans _ secondA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    have same := frameB.prefix spaceA (i:=24+8*p.w+8*i+j) (by unfold tableStart;omega)
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · exact basisB.table
 refine WP.mono (WP.keep [.x0] (Q:=fun t =>t.gpr .x0=1#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun
 · rintro t ⟨⟨status,mem⟩,rest⟩
   exact ⟨status,by rw [mem];exact canonical,
    by rw [mem];exact (PublicFrame.of_context frameA (by omega)).trans (PublicFrame.of_build frameB),
    ((restA.trans restB).trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
