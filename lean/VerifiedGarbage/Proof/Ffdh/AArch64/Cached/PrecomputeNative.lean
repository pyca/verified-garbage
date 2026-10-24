module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeArithmetic
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeEntry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataWorkspace
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicSource
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Omega

/-! Functional composition of the complete native public precomputation routine. -/
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
