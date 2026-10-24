module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

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
 have fit : 8*n+8*p.w≤2^64 := by have := p.width;omega
 have offFit : 8*n<2^64 := by have := p.positive;omega
 have outside (i : Nat) (hi : i<8*p.w) : p.Z≤ofs p.B (off p.ctx (8*n)+BitVec.ofNat 64 i) := by
  have h := space.outside (8*n+i) (by omega)
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using h
 have sourceInside (i : Nat) (hi : i<p.w) (b : Nat) (hb : b<8) :
  ofs p.B (off p.B (slot p.w a+8*i)+BitVec.ofNat 64 b)<p.Z := by
  rw [ofs_off p.B (by have := good.scr.nowrap;omega)]
  omega
 refine WP.mono (copyWords_ok source output count (by have := p.positive;omega) p.width fit
  (fun i hi => good.scr.ld (by omega))
  (fun i hi => by
   have rd := space.writable (n+i) (by omega)
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
  fun i hi => (header (sArr i) (by unfold sArr;omega)).trans (good.hdr.harr i hi)⟩,
  value,frame,unchanged,?_,totalRest⟩
 simpa only [Nat.mul_add] using pointer

end VG.Proof.Ffdh.AArch64.Cached
