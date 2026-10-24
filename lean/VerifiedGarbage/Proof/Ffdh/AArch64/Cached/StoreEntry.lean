module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Store a reduced residue into its canonical context entry, preserving the arithmetic workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem storeEntry_ok {s : State} {B ctx : Addr} {Z w a j : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31) (array : a<8)
 (context : word s.mem B (8*sCtx)=ctx) (digit : s.gpr .x3=BitVec.ofNat 64 j)
 (fit : entryOffset w j+8*w≤2^64)
 (writable : ∀ i<w,InRegions s.wr (off ctx (entryOffset w j+8*i)) 8)
 (outside : ∀ i<8*w,Z≤ofs B (off ctx (entryOffset w j)+BitVec.ofNat 64 i)) :
 WP isa (storeEntry a) s fun t =>
 Good t B Z w mi ∧ wv t.mem ctx (entryOffset w j) w=wv s.mem B (slot w a) w ∧
 Outside ctx (entryOffset w j) (8*w) s.mem t.mem ∧
 (∀ x,ofs B x<Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 have arrHdr : sArr a<32 := by unfold sArr;omega
 have arrayRoom : slot w a+8*(w+2)≤Z := Nat.le_trans (slot_le array) room
 have offFit : entryOffset w j<2^64 := by omega
 have sourceInside (i : Nat) (hi : i<w) (b : Nat) (hb : b<8) :
  ofs B (off B (slot w a+8*i)+BitVec.ofNat 64 b)<Z := by
  rw [ofs_off B (by have := good.scr.nowrap;omega)]
  omega
 unfold storeEntry
 rw [WP.seq_iff,WP.block_append_iff]
 refine WP.mono (entryPtr_ok good room context digit) ?_
 rintro u ⟨⟨ptrU,countU,memU⟩,restU⟩
 refine WP.mono (WP.keep [.x16] (Q:=fun v => v.gpr .x16=off B (slot w a) ∧ v.mem=u.mem) ?_ rfl rfl rfl) ?_
 · brun [restU.rd,restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,hdr_enc arrHdr,
    good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot w 8 arrHdr;omega),memU,good.hdr.harr a array]
 · rintro v ⟨⟨srcV,memV⟩,restV⟩
   have rest := restU.trans restV
   have mem : v.mem=s.mem := memV.trans memU
   refine WP.mono (copyWords_ok (S:=B) (D:=ctx) (eS:=slot w a) (eD:=entryOffset w j) (w:=w) srcV ((restV.gpr .x17 (by decide)).trans ptrU)
    ((restV.gpr .x12 (by decide)).trans countU) (by omega) size fit
    (fun i hi => by rw [rest.rd,rest.wr];exact good.scr.ld (by omega))
    (fun i hi => by rw [rest.wr];exact writable i hi)
    (fun i hi b hb => (outside_shift_iff ctx _ offFit fit).mpr
     (le_ofs_of_sep outside (sourceInside i hi b hb)))) ?_
   rintro t ⟨value,_,frame,_,_,restT⟩
   have totalRest : Keep mmRegs s t := (rest.trans restT).mono (by simp [mmRegs])
   have totalFrame : Outside ctx (entryOffset w j) (8*w) s.mem t.mem := by rw [←mem];exact frame
   have unchanged (x : Addr) (hx : ofs B x<Z) : t.mem x=s.mem x :=
    totalFrame x ((outside_shift_iff ctx x offFit fit).mpr (le_ofs_of_sep outside hx))
   have header (i : Nat) (hi : i<32) : word t.mem B (8*i)=word s.mem B (8*i) := by
    apply Mem.readW_congr
    intro b hb
    apply unchanged
    have headerFit := hdr_lt_slot w 8 hi
    have scratchFit := good.scr.nowrap
    rw [ofs_off B (by omega)]
    omega
   refine ⟨⟨good.scr.congr totalRest.wr,(totalRest.gpr .x0 (by simp [mmRegs])).trans good.x0,
    (header sW (by decide)).trans good.hdr.hw,(header sMinv (by decide)).trans good.hdr.hminv,
    fun i hi => (header (sArr i) (by unfold sArr;omega)).trans (good.hdr.harr i hi)⟩,?_,totalFrame,unchanged,totalRest⟩
   rw [mem] at value
   exact value

end VG.Proof.Ffdh.AArch64.Cached
