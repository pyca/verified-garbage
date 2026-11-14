module
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb

/-! ### `MlKem.AArch64.FixedHash.AbsorbStep`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (xorAt)

theorem absorbWord_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+8≤p.len) (ho : p.off+i<65536) (hpos : pos+8≤rate)
 (hd : (st+pos)%8=0 ∧ st+pos<32768) :
 WP isa (.block (ptrTo .x2 p.base (p.off+i) ++
   ([.ldr .x .x9 .x2 0,.ldr .x .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,
     .str .x .x9 sc (st+pos)] : List Instr))) s fun t=>
 Kept [STr sc st s₀] s t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
   xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos
     (bytesAt s.mem (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) 8) := by
 have ns : sc≠.x2 ∧ sc≠.x9 ∧ sc≠.x10 := by
   have all : ∀r∈preserved,r≠.x2 ∧ r≠.x9 ∧ r≠.x10 := by decide
   exact all sc hS.hsc.1
 have nb : p.base≠.x2 := (pres_not hp.base.1).2.2.1
 have gs := hg.cs sc hS.hsc.1 hS.hsc.2
 have gb := hg.cs p.base hp.base.1 hp.base.2
 have addr : s.gpr sc+BitVec.ofNat 64 (st+pos)=s₀.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos := by
   rw [gs,BitVec.add_assoc,←BitVec.ofNat_add]
 have cs : (STr sc st s₀).Contains (s.gpr sc+BitVec.ofNat 64 (st+pos)) 8 := by
   rw [addr]
   exact Offset.contains_base _ (by have:= (rate_bounds hS.hrate).2; omega_using [hpos, this]) (by have:= (rate_bounds hS.hrate).2; omega_using [hd])
 refine WP.mono (absorbWord_ok nb ns.1 ns.2.1 ns.2.2 ho hd ?_ ?_) fun t ⟨kt,mt⟩=> ?_
 · rw [hg.rd,hg.wr,gb]
   apply hp.cov
   refine ⟨preg s₀ p,List.mem_singleton_self _,?_⟩
   rw [BitVec.ofNat_add,←BitVec.add_assoc]
   exact Offset.contains_base _ hi (by have:=hp.len; omega_using [ho])
 · rw [hg.wr]
   exact hS.cov _ _ ⟨_,List.mem_cons_self ..,cs⟩
 · refine ⟨⟨fun r hr hn=>kt.gpr r (by revert r hr; decide),kt.sp,kt.rd,kt.wr,?_,kt.vcs⟩,?_⟩
   · rw [mt]
     exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cs
   · rw [mt,addr,gb]
     exact absorbWord_state _ _ _ (by have:= (rate_bounds hS.hrate).2; omega_using [hpos, this])
theorem absorbByte_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+1≤p.len) (ho : p.off+i<65536) (hpos : pos+1≤rate)
 (hd : st+pos<4096) :
 WP isa (.block (ptrTo .x2 p.base (p.off+i) ++
   ([.ldrb .x9 .x2 0,.ldrb .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,
     .strb .x9 sc (st+pos)] : List Instr))) s fun t=>
 Kept [STr sc st s₀] s t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
   xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos
     (bytesAt s.mem (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) 1) := by
 have ns : sc≠.x2 ∧ sc≠.x9 ∧ sc≠.x10 := by
   have all : ∀r∈preserved,r≠.x2 ∧ r≠.x9 ∧ r≠.x10 := by decide
   exact all sc hS.hsc.1
 have nb : p.base≠.x2 := (pres_not hp.base.1).2.2.1
 have gs := hg.cs sc hS.hsc.1 hS.hsc.2
 have gb := hg.cs p.base hp.base.1 hp.base.2
 have addr : s.gpr sc+BitVec.ofNat 64 (st+pos)=s₀.gpr sc+BitVec.ofNat 64 st+BitVec.ofNat 64 pos := by
   rw [gs,BitVec.add_assoc,←BitVec.ofNat_add]
 have cs : (STr sc st s₀).Contains (s.gpr sc+BitVec.ofNat 64 (st+pos)) 1 := by
   rw [addr]
   exact Offset.contains_base _ (by have:= (rate_bounds hS.hrate).2; omega_using [hpos, this]) (by have:= (rate_bounds hS.hrate).2; omega_using [hd])
 refine WP.mono (absorbByte_ok nb ns.1 ns.2.1 ns.2.2 ho hd ?_ ?_) fun t ⟨kt,mt⟩=> ?_
 · rw [hg.rd,hg.wr,gb]
   apply hp.cov
   refine ⟨preg s₀ p,List.mem_singleton_self _,?_⟩
   rw [BitVec.ofNat_add,←BitVec.add_assoc]
   exact Offset.contains_base _ hi (by have:=hp.len; omega_using [ho])
 · rw [hg.wr]
   exact hS.cov _ _ ⟨_,List.mem_cons_self ..,cs⟩
 · refine ⟨⟨fun r hr hn=>kt.gpr r (by revert r hr; decide),kt.sp,kt.rd,kt.wr,?_,kt.vcs⟩,?_⟩
   · rw [mt]
     exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cs
   · rw [mt,addr,gb]
     simpa [bytesAt,Proof.Sha3.xorAt_single] using
       absorbByte_state s.mem (s₀.gpr sc+BitVec.ofNat 64 st)
         (s₀.gpr p.base+BitVec.ofNat 64 (p.off+i)) (by have:= (rate_bounds hS.hrate).2; omega_using [hpos, this])
end VG.Proof.MlKem.AArch64.FixedHash

end

end

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
 rw [show p.len-i=n+(p.len-(i+n)) by omega_using [hn],
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
 · have:=hp.len; omega_using [hn, this]

theorem action_piece_ok {s₀ s : State} {sc : Reg} {st wk rate pos i : Nat} {p : Piece} {w : Bool}
 (hS : HSetup sc st wk rate s₀) (hp : PieceOk sc st wk s₀ false p) (hg : Rg s₀ s)
 (hi : i+width w≤p.len) (ho : p.off+p.len≤65536) (hpos : pos+width w≤rate)
 (hw : w=true→i%8=0 ∧ pos%8=0) (ha : st%8=0) (hb : st+rate≤4096) :
 WP isa (.block (actionCode sc st (action p i pos w))) s fun t=>
 Kept [STr sc st s₀] s t ∧ stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
 xorAt (stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)) pos (chunkBytes s p i (width w)) := by
 have gb := hg.cs p.base hp.base.1 hp.base.2
 cases w <;> simp only [actionCode,action,width,Bool.false_eq_true,ite_false,ite_true,chunkBytes] at * <;> simp only [gb]
 · exact absorbByte_piece_ok (s₀:=s₀) (s:=s) (sc:=sc) (st:=st) (wk:=wk) (rate:=rate) (pos:=pos) (i:=i) (p:=p) hS hp hg hi (by omega_using [ho, hi]) hpos
     (by omega_using [hb, hpos])
 · have hw' : i%8=0 ∧ pos%8=0 := by simpa using hw
   have hm := hw'.2
   apply absorbWord_piece_ok (s₀:=s₀) (s:=s) (sc:=sc) (st:=st) (wk:=wk) (rate:=rate) (pos:=pos) (i:=i) (p:=p) hS hp hg hi (by omega_using [ho, hi]) hpos
   exact ⟨by omega_using [ha, hw'],by omega_using [hb, hpos]⟩

end VG.Proof.MlKem.AArch64.FixedHash
