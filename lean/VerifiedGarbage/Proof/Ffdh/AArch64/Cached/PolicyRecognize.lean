module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBound
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Omega

/-! Full native exact-group recognition, including the conservative general bound. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.RsaKeyGen (bitLength)

private theorem exec_adrSym (s : State) (r : Reg) (sym : String) :
 exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) := rfl

private theorem byteCount_bound : ∀ b : Byte,bitLength b.toNat≤8 := by decide +kernel

theorem policyRecognize_ok {s : State} {B domPtr : Addr} {Z k dl L : Nat} {dom bs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^28) (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (pointer : word s.mem B (8*sDom)=domPtr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (domainSource : Source domPtr dom s)
 (domainOutside : ∀ i<dom.length,8*sBits+8≤ofs B (domPtr+BitVec.ofNat 64 i))
 (source : Source (if dl=2*k then domPtr else off domPtr (2*k)) bs s) (bsLength : bs.length=k)
 (inside : L<bs.length) (zeros : ∀ i<L,bs.getD i 0=0#8) (nonzero : bs.getD L 0≠0#8)
 (records : PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa Policy.recognize s fun t =>
 word t.mem B (8*sBits)=BitVec.ofNat 64
  (policyWidth (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat) k dom Policy.groups) ∧
 Outside B (8*sBits) 8 s.mem t.mem ∧ Keep recordClobbers s t := by
 let N := 8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat
 unfold Policy.recognize
 rw [WP.seq_iff]
 refine WP.mono_syms (policyBound_ok scratch room base positive (by omega) shape pointer length domainLength
  source bsLength inside zeros nonzero) ?_
 rintro a ⟨memA,restA⟩ symsA
 have frameA : Outside B (8*sBits) 8 s.mem a.mem := by rw [memA];exact writeW_outside _ _ _ (by decide)
 have headerA (i : Nat) (hi : i<32) (different : i≠sBits) : word a.mem B (8*i)=word s.mem B (8*i) :=
  header_other frameA (by decide) hi different
 have sourceA := domainSource.after_outside frameA restA domainOutside
 have recordsA := records.after_header frameA restA
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x4,.x7] (Q:=fun b =>
  b.gpr .x4=s.syms Policy.tableSym ∧ b.gpr .x7=BitVec.ofNat 64 Policy.groups.length ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [exec_adrSym,symsA,show Policy.groups.length=10 from rfl]
 · rintro b ⟨⟨ptrB,countB,memB⟩,restB⟩
   have rest := restA.trans restB
   have cap : word b.mem B (8*sBits)=BitVec.ofNat 64 N := by rw [memB,memA,word_writeW_self]
   refine WP.mono (policyLoop_ok (scratch.congr rest.wr) room ((rest.gpr .x0 (by decide)).trans base)
    (sourceA.of_mem memB restB) (recordsA.after_mem memB restB) (by omega) positive size
    (by rw [memB,headerA sDom (by decide) (by decide)];exact pointer)
    (by rw [memB,headerA sDL (by decide) (by decide),domainLength,domLength])
    (by rw [memB,headerA sLen (by decide) (by decide)];exact length) cap
    (by have h := byteCount_bound (bs.getD L 0#8);dsimp [N];omega) ptrB countB (by decide) (by decide)) ?_
   rintro t ⟨widthT,frameT,restT⟩
   refine ⟨widthT,?_,(rest.trans restT).mono (by simp [recordClobbers])⟩
   have frameB : Outside B (8*sBits) 8 s.mem b.mem := by rw [memB];exact frameA
   exact frameB.trans frameT

end VG.Proof.Ffdh.AArch64.Cached
