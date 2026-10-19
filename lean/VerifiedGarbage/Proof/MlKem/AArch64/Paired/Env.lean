module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset

/-! # Rejection-loop coverage within the paired sampler scratch

The vector load may read four bytes beyond the logical stream; the sampler
already owns those bytes, and the decoded candidates use only the stream.
-/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64

/-- Instantiate all scalar/vector memory obligations for initial, continuation
and singleton rejection segments. -/
theorem rejection_envW {w16 : Bool} {s : State} {p out : Addr} {off N : Nat} {B : Nat → Byte}
    (hn : N≤280) (hf : off+3*N+4≤2048)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (bytes : ∀i<3*N,s.mem ((p+BitVec.ofNat 64 off)+BitVec.ofNat 64 i)=B i)
    (tr : ∀mask<256,InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16)
    (tv : ∀mask<256,s.mem.read (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16=Rej8.tableVec mask)
    (td : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint (polyRegion out)) :
    Rej8.EnvW w16 N B (p+BitVec.ofNat 64 off) out s := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  have ir {o l : Nat} (h : o+l≤2048) : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 o) l := by
    obtain ⟨r,hr,hc⟩ := iw h; exact ⟨r,List.mem_append_right _ hr,hc⟩
  refine ⟨⟨bytes,?_,?_,?_,hn⟩,?_,?_,tr,tv,td⟩
  · intro i hi; rw [BitVec.add_assoc,← BitVec.ofNat_add]; exact ir (by omega)
  · intro i hi
    exact Noise.inScratch ho (by cases w16 <;> simp [VG.Proof.MlKem.cs_eq] <;> omega :
      VG.Proof.MlKem.cs w16*i+4≤1024) (by decide)
  · exact hd.sub_left (Offset.sub_base p (by omega))
  · intro t ht; rw [BitVec.add_assoc,← BitVec.ofNat_add]; exact ir (by omega)
  · intro i hi
    exact Noise.inScratch ho (by cases w16 <;> simp [VG.Proof.MlKem.cs_eq] at hi ⊢ <;> omega :
      VG.Proof.MlKem.cs w16*i+16≤1024) (by decide)

end VG.Proof.MlKem.AArch64.Paired
