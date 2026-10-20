module
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbStep
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep xorAt)

def chunkBytes (s : State) (p : Piece) (i n : Nat) : List Byte :=
 bytesAt s.mem (s.gpr p.base+BitVec.ofNat 64 (p.off+i)) n

def remainingBytes (s : State) : List Piece → Nat → List Byte
 | [],_=>[]
 | p::ps,i=>chunkBytes s p i (p.len-i) ++ (ps.map (pbytes s)).flatten

theorem remaining_skip (s : State) (p : Piece) (ps : List Piece) :
 remainingBytes s (p::ps) p.len=remainingBytes s ps 0 := by
 cases ps with
 | nil => simp [remainingBytes,chunkBytes,bytesAt]
 | cons q qs => simp [remainingBytes,chunkBytes,pbytes,bytesAt]

theorem remaining_step (s : State) (p : Piece) (ps : List Piece) {i n : Nat}
 (hn : i+n≤p.len) : remainingBytes s (p::ps) i=
 chunkBytes s p i n ++ remainingBytes s (p::ps) (i+n) := by
 simp only [remainingBytes,chunkBytes]
 rw [show p.len-i=n+(p.len-(i+n)) by omega,
   Proof.Sha3.AArch64.Stream.Absorb.bytesAt_add,List.append_assoc,
   BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc]

theorem chunkBytes_frame {s₀ s : State} {sc : Reg} {st wk : Nat} {p : Piece} {i n : Nat}
 (hp : PieceOk sc st wk s₀ false p) (hk : Kept [STr sc st s₀,WKr sc wk s₀] s₀ s)
 (hn : i+n≤p.len) : chunkBytes s p i n=chunkBytes s₀ p i n := by
 unfold chunkBytes
 rw [hk.cs p.base hp.base.1 hp.base.2]
 have sub : Region.Sub ⟨s₀.gpr p.base+BitVec.ofNat 64 (p.off+i),n⟩ (preg s₀ p) := by
   simpa only [preg,BitVec.add_assoc,←BitVec.ofNat_add] using
     (Offset.sub_base (s₀.gpr p.base+BitVec.ofNat 64 p.off) (d:=i) hn)
 apply VG.Proof.MlKem.bytesAt_frame hk.frame
 · intro r hr
   rcases mem2' hr with rfl|rfl
   · exact hp.dst.sub_left sub
   · exact hp.dwk.sub_left sub
 · have:=hp.len; omega

theorem action_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece} {w : Bool}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+width w≤p.len) (ho : p.off+p.len≤65536) (hpos : pos+width w≤rate)
 (hw : w=true→i%8=0 ∧ pos%8=0) (ha : st%8=0) (hb : st+rate≤4096) :
 WP isa (.block (actionCode sc st (action p i pos w))) s fun t=>
 Kept [STr sc st s₀] s t ∧ stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
 xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos (chunkBytes s p i (width w)) := by
 have gb := hg.cs p.base hp.base.1 hp.base.2
 cases w <;> simp only [actionCode,action,width,Bool.false_eq_true,ite_false,ite_true,chunkBytes] at * <;> simp only [gb]
 · exact absorbByte_piece_ok (s₀:=s₀) (s:=s) (sc:=sc) (st:=st) (wk:=wk) (rate:=rate) (pos:=pos) (i:=i) (p:=p) hS hp hg hi (by omega) hpos
     (by omega)
 · have hw' : i%8=0 ∧ pos%8=0 := by simpa using hw
   have hm := hw'.2
   apply absorbWord_piece_ok (s₀:=s₀) (s:=s) (sc:=sc) (st:=st) (wk:=wk) (rate:=rate) (pos:=pos) (i:=i) (p:=p) hS hp hg hi (by omega) hpos
   exact ⟨by omega,by omega⟩

end VG.Proof.MlKem.AArch64.FixedHash
