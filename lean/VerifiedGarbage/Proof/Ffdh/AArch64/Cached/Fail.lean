module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Clear
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! A rejected scalar returns 2 and zeroes both complete outputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fail_ok {s : State} {B xp yp : Addr} {Z k : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (x : word s.mem B (8*sX)=xp) (y : word s.mem B (8*sY)=yp) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (writeX : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,k≤ofs yp (xp+BitVec.ofNat 64 i)) :
 WP isa Generate.fail s fun t =>
 t.gpr .x0=2#64 ∧ Spec.Rsa.bytesAt t.mem xp k=List.replicate k 0 ∧
 Spec.Rsa.bytesAt t.mem yp k=List.replicate k 0 ∧ Frame [⟨xp,k⟩,⟨yp,k⟩] s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 unfold Generate.fail
 rw [WP.seq_iff]
 refine WP.mono (clear_ok scratch room base positive size (by decide : sX<32) x length writeX) ?_
 rintro a ⟨zeroX,frameX,restX⟩
 have sameScratch (q : Addr) (hq : ofs B q<Z) : a.mem q=s.mem q :=
  frameX q (Or.inr (by have sep : k≤ofs xp q := le_ofs_of_sep outsideX hq;omega))
 have sameHeader (i : Nat) (hi : i<32) : word a.mem B (8*i)=word s.mem B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega) sameScratch (by omega)
 rw [WP.seq_iff]
 refine WP.mono (clear_ok (scratch.congr restX.wr) room ((restX.gpr .x0 (by decide)).trans base) positive size
  (by decide : sY<32) ((sameHeader sY (by decide)).trans y) ((sameHeader sLen (by decide)).trans length)
  (fun i hi =>by rw [restX.wr];exact writeY i hi)) ?_
 rintro b ⟨zeroY,frameY,restY⟩
 have xBytes : Spec.Rsa.bytesAt b.mem xp k=List.replicate k 0 := by
  rw [←zeroX]
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
    exact frameY _ (Or.inr (by have := separate i bound;omega))
 have frame (ptr : Addr) {m m' : Mem} (h : Outside ptr 0 k m m')
  (member : (⟨ptr,k⟩ : Region)∈[⟨xp,k⟩,⟨yp,k⟩]) : Frame [⟨xp,k⟩,⟨yp,k⟩] m m' := by
  intro q hq
  apply h q
  right
  have no := hq ⟨ptr,k⟩ member
  change ¬ofs ptr q+1≤k at no
  omega
 refine WP.mono (WP.keep [.x0] (Q:=fun t =>t.gpr .x0=2#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun
 · rintro t ⟨⟨status,mem⟩,rest⟩
   exact ⟨status,by rw [mem];exact xBytes,by rw [mem];exact zeroY,
    by rw [mem];exact (frame xp frameX (by simp)).trans (frame yp frameY (by simp)),
    ((restX.trans restY).trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
