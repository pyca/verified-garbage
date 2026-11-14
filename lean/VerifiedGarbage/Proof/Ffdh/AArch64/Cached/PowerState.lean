module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectScan
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
public import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont

/-! ### `Ffdh.AArch64.Cached.Select`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SelectLayout`, which only this module used -/

section

/-! The packed immutable context lies outside the existing Montgomery workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem selectEnv_good {s : State} {B table : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 SelectEnv B table (off B (slot w 5)) w s := by
 have arrayRoom : slot w 5+8*(w+2)≤Z := Nat.le_trans (slot_le (by decide : 5<8)) room
 have size : Z≤2^64 := by have := good.scr.nowrap;omega
 have hd : slot w 5<2^64 := by omega
 have fit : slot w 5+8*w≤2^64 := by omega
 refine ⟨good.x0,good.hdr.harr 5 (by decide),good.hdr.hw,?_,?_,readSource,?_,?_,?_,?_,?_⟩
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sArr 5<32 by decide);omega)
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega)
 · intro i hi
   rw [off_off]
   exact good.scr.ld (by omega)
 · intro i hi
   rw [off_off]
   exact good.scr.st (by omega)
 · intro j hj i hi b hb
   exact (outside_shift_iff B _ hd fit).mp (Or.inr (by have := sourceOutside j hj i hi b hb;omega))
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sArr 5<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sArr 5<32 by decide)
   omega
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sW<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sW<32 by decide)
   omega

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Complete canonical-context selection into the existing Montgomery operand array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem select_ok {s : State} {B table : Addr} {Z w v : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (width : w<2^31) (hv : v<32)
 (tablePtr : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sTab)=table)
 (digit : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sD)=BitVec.ofNat 64 v)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.select s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=wv s.mem table (8*w*v) w ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 have convert (m : Mem) (i : Nat) : word m (off B (slot w 5)) (8*i)=word m B (slot w 5+8*i) := by
  simp only [word,VG.Proof.Bignum.off_off]
 have nowrap : slot w 5+8*(w+2)≤2^64 := by
  have := good.scr.nowrap
  have := slot_le (w:=w) (by decide : 5<8)
  omega_arith
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.select
 rw [WP.seq_iff]
 refine WP.mono (const_ok good room positive width (by decide : 5<8) (by decide : 0<2^16)) ?_
 rintro u ⟨goodU,zeroU,frameU,restU⟩
 have arraysU : Arrays B w [5] s.mem u.mem := Arrays.of_outside (j:=5) (by simp) frameU (by omega_using []) (by omega_using [])
 have headerU (i : Nat) (hi : i<32) : word u.mem B (8*i)=word s.mem B (8*i) :=
  frameU.word (Or.inl (hdr_lt_slot w 5 hi)) (by omega_using [hi])
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x9,.x10,.x11] (Q:=fun z =>
  z.gpr .x9=table ∧ z.gpr .x10=BitVec.ofNat 64 v ∧ z.gpr .x11=0#64 ∧ z.mem=u.mem)
  ?_ rfl rfl rfl) ?_
 · brun [goodU.x0,hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide),
   hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sTab)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide);omega_using [room, this]),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sD)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide);omega_using [room, this]),
   headerU VG.Impl.Ffdh.AArch64.Cached.sTab (by decide),
   headerU VG.Impl.Ffdh.AArch64.Cached.sD (by decide),tablePtr,digit]
 · rintro z ⟨⟨pointerZ,digitZ,candidateZ,memZ⟩,restZ⟩
   have restUZ := restU.trans restZ
   have goodZ : Good z B Z w mi :=
    ⟨goodU.scr.congr restZ.wr,(restZ.gpr .x0 (by decide)).trans goodU.x0,memZ ▸ goodU.hdr⟩
   have envZ : SelectEnv B table (off B (slot w 5)) w z := selectEnv_good goodZ room positive
    (fun j hj i hi => by rw [restUZ.rd,restUZ.wr];exact readSource j hj i hi) sourceOutside
   have zeros : ∀ i<w, word z.mem (off B (slot w 5)) (8*i)=0#64 := by
    intro i hi
    rw [convert,memZ]
    exact (wv_eq_zero_iff _ _ _ _).mp zeroU i hi
   refine WP.mono (selectScan_ok z envZ positive (by omega_using [width]) hv pointerZ digitZ candidateZ zeros) ?_
   rintro t ⟨_,words,frame,restT⟩
   have frameZ : Outside B (slot w 5) (8*w) z.mem t.mem :=
    outside_to_workspace (by omega_using [nowrap]) (by omega_using [nowrap]) frame
   have arraysZ : Arrays B w [5] z.mem t.mem := Arrays.of_outside (j:=5) (by simp) frameZ (by omega_using []) (by omega_using [])
   have totalArrays : Arrays B w [5] s.mem t.mem := by
    rw [memZ] at arraysZ
    exact arraysU.trans arraysZ
   have totalRest : Keep mmRegs s t := (restUZ.trans restT).mono (by simp [selectClobbers,mmRegs])
   refine ⟨good_after_arrays good totalArrays totalRest
    ((totalRest.gpr .x0 (by decide)).trans good.x0),?_,totalArrays,totalRest⟩
   apply wv_congr2
   intro i hi
   rw [←convert,words i hi,memZ]
   exact Mem.readW_congr fun b hb => InScr.of_arrays arraysU room (by simp) _ (sourceOutside v hv i hi b hb)

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The same Montgomery residues and bounds used by RSA, with a fixed-base exponent. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Parameters where
 B : Addr
 Z : Nat
 w : Nat
 mi : BitVec 64
 P : Nat
 G : Nat
 N : Nat
 k : Nat
 src : Addr
 ctx : Addr
 table : Addr
 room : slot w 8≤Z
 positive : 2≤w
 width : w<2^31
 modulusPositive : 1<P
 coprime : Nat.Coprime (2^(64*w)) P

structure ModState (p : Parameters) (s : State) : Prop where
 good : Good s p.B p.Z p.w p.mi
 modulus : wv s.mem p.B (slot p.w 0) p.w=p.P
 inverse : ((word s.mem p.B (slot p.w 0)).toNat*p.mi.toNat+1)%2^64=0
 one : wv s.mem p.B (slot p.w 7) p.w=1
 r2 : wv s.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P

structure Power (p : Parameters) (E : Nat) (s : State) : Prop extends ModState p s where
 bound : wv s.mem p.B (slot p.w 6) p.w<p.P
 value : wv s.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P

theorem ModState.after_arrays {p : Parameters} {s t : State} {js : List Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) : ModState p t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv_of_not_mem (by decide) zero nowrap).trans h.modulus
 · rw [frame.word0_of_not_mem (by decide) zero nowrap (by have := p.positive;omega_using [this])]
   exact h.inverse
 · exact (frame.wv_of_not_mem (by decide) one nowrap).trans h.one
 · exact (frame.wv_of_not_mem (by decide) r2 nowrap).trans h.r2

theorem ModState.after_header {p : Parameters} {s t : State} {i : Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : ModState p t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have below (j : Nat) : 8*i+8≤slot p.w j := hdr_lt_slot _ _ hi
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega_using [nowrap, this])).trans h.modulus
 · rw [frame.word (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega_using [nowrap, this])]
   exact h.inverse
 · exact (frame.wv (Or.inr (below 7)) (by have := slot_le (w:=p.w) (by decide : 7<8);omega_using [nowrap, this])).trans h.one
 · exact (frame.wv (Or.inr (below 4)) (by have := slot_le (w:=p.w) (by decide : 4<8);omega_using [nowrap, this])).trans h.r2

theorem Power.after_arrays {p : Parameters} {E : Nat} {s t : State} {js : List Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) (y : 6∉js) : Power p E t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have same := frame.wv_of_not_mem (by decide : 6<8) y nowrap
 exact ⟨h.toModState.after_arrays good frame zero one r2,by rw [same];exact h.bound,by rw [same];exact h.value⟩

theorem Power.after_header {p : Parameters} {E : Nat} {s t : State} {i : Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : Power p E t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have same : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  frame.wv (Or.inr (hdr_lt_slot _ _ hi)) (by have := slot_le (w:=p.w) (by decide : 6<8);omega_using [nowrap, this])
 exact ⟨h.toModState.after_header good frame hi,by rw [same];exact h.bound,by rw [same];exact h.value⟩

/-- One genuine Montgomery square doubles the encoded exponent. -/
theorem power_square (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 6) s fun t =>
 Power p (2*E) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 6<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse h.bound) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded p.coprime boundT h.value productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

/-- A selected residue adds its canonical comb exponent. -/
theorem power_product (M : Mont) {p : Parameters} {E F : Nat} {s : State} (h : Power p E s)
 (selected : wv s.mem p.B (slot p.w 5) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 6 5) s fun t =>
 Power p (E+F) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound5 : wv s.mem p.B (slot p.w 5) p.w<p.P := by rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega_using [this])
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 5<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound5) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime boundT h.value selected productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
