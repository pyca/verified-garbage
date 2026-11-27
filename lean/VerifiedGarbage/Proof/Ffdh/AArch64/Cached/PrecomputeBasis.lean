module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StoreEntry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState

/-! ### `Ffdh.AArch64.Cached.PrecomputeSquares`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeSquareLoop`, which this module and modules that import it used -/

section

/-! A public number of Montgomery squares advances a comb tooth by 2^rows. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

def squareRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 2,8*(w+2)),(slot w 3,8*(w+2)),(slot w 6,8*(w+2)),(8*sI,8)]

structure SquareInv (s0 : State) (p : Parameters) (E n j : Nat) (s : State) : Prop where
 power : Power p (E*2^j) s
 counter : Counter p.B (n-j) s
 frame : Frm p.B (squareRanges p.w) s0.mem s.mem
 keep : Keep mmRegs s0 s

theorem precomputeSquareStep (M : Mont) {s0 s : State} {p : Parameters} {E n j : Nat}
 (size : n<2^64) (inside : j<n) (h : SquareInv s0 p E n j s) :
 WP isa (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI])) s fun t =>
 SquareInv s0 p E n (j+1) t ∧ ((t.gpr .x3).toNat≠0 ↔ j+1≠n) := by
 rw [WP.seq_iff]
 refine WP.mono (power_square M h.power) ?_
 rintro u ⟨power,arrays,rest⟩
 have counterU : Counter p.B (n-j) u := (arrays_header arrays (by decide)).trans h.counter
 refine WP.mono (decrement_control_ok power.good p.room (by decide : 16≤sI) (by decide : sI<32)
  (by omega_using [inside]) counterU) ?_
 rintro t ⟨good,counter,index,frame,keep⟩
 have powerT := power.after_header good frame (by decide : sI<32)
 have exponent : 2*(E*2^j)=E*2^(j+1) := by rw [Nat.pow_succ];ring
 rw [exponent] at powerT
 have remaining : n-j-1=n-(j+1) := by omega_using []
 rw [remaining] at counter
 refine ⟨⟨powerT,counter,?_,((h.keep.trans rest).trans keep).mono (by decide)⟩,?_⟩
 · exact (h.frame.trans (Frm.of_arrays arrays (by simp [squareRanges]))).trans
    (Frm.of_outside frame (by simp [squareRanges]))
 · rw [index,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [size] : n-j-1<2^64)]
   omega_using [inside]

theorem precomputeSquareLoop_ok (M : Mont) {s : State} {p : Parameters} {E n : Nat}
 (power : Power p E s) (counter : Counter p.B n s) (positive : 0<n) (size : n<2^64) :
 WP isa (.loop (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI]))
  (.nonzero .x .x3)) s fun t =>
 Power p (E*2^n) t ∧ Counter p.B 0 t ∧ Frm p.B (squareRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 have init : SquareInv s p E n 0 s := by
  refine ⟨?_,?_,Frm.refl _ _ _,Keep.refl _ _⟩
  · simpa only [Nat.pow_zero,Nat.mul_one] using power
  · simpa only [Nat.sub_zero] using counter
 refine WP.mono (count_loop positive (SquareInv s p E n)
  (fun j hj s h => precomputeSquareStep M size hj h) init) ?_
 rintro t h
 exact ⟨h.power,by simpa only [Nat.sub_self] using h.counter,h.frame,h.keep⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Complete precomputation of the next comb tooth using the shared squaring kernel. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/CounterInit.lean`, which only this module imported.
section

/-! Initialize the public squaring counter from the cached row-count header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem counterInit_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (rows : word s.mem B (8*sRows)=BitVec.ofNat 64 n) :
 WP isa (.block [ldh .x3 sRows,sth .x3 sI]) s fun t =>
 Good t B Z w mi ∧ Counter B n t ∧ Outside B (8*sI) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 change WP isa (.block ([ldh .x3 sRows]++[sth .x3 sI])) s _
 rw [WP.block_append_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 n ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sRows<32 by decide),header_read good room (show sRows<32 by decide),rows]
 · rintro u ⟨⟨value,memU⟩,restU⟩
   have goodU : Good u B Z w mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (store_control_ok goodU room (by decide : 16≤sI) (by decide : sI<32) .x3) ?_
   rintro t ⟨goodT,memT,frame,restT⟩
   refine ⟨goodT,?_,?_,(restU.trans restT).mono (by simp)⟩
   · unfold Counter
     rw [memT,word_writeW_self,value]
   · rw [←memU];exact frame

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def basisSquareRanges (w : Nat) : List (Nat × Nat) := squareRanges w++[(slot w 5,8*(w+2))]

theorem precomputeSquares_ok (M : Mont) {s : State} {p : Parameters} {E n : Nat}
 (basis : Basis p E s) (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 n) (positive : 0<n) (size : n<2^64) :
 WP isa (Precompute.squares M.mm) s fun t =>
 Basis p (E*2^n) t ∧ Power p (E*2^n) t ∧
 Frm p.B (basisSquareRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.squares
 rw [WP.seq_iff]
 refine WP.mono (basis_to_power basis) ?_
 rintro a ⟨powerA,_,frameA,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (counterInit_ok powerA.good p.room ((arrays_header frameA (by decide)).trans rows)) ?_
 rintro b ⟨goodB,counterB,frameB,restB⟩
 have powerB := powerA.after_header goodB frameB (by decide : sI<32)
 rw [WP.seq_iff]
 refine WP.mono (precomputeSquareLoop_ok M powerB counterB positive size) ?_
 rintro c ⟨powerC,_,frameC,restC⟩
 refine WP.mono (power_to_basis powerC) ?_
 rintro t ⟨basisT,powerT,frameT,restT⟩
 have first : Frm p.B (basisSquareRanges p.w) s.mem a.mem :=
  Frm.of_arrays frameA (by simp [basisSquareRanges,squareRanges])
 have second : Frm p.B (basisSquareRanges p.w) a.mem b.mem :=
  Frm.of_outside frameB (by simp [basisSquareRanges,squareRanges])
 have third : Frm p.B (basisSquareRanges p.w) b.mem c.mem :=
  frameC.mono (fun r hr => List.mem_append_left _ hr)
 have fourth : Frm p.B (basisSquareRanges p.w) c.mem t.mem :=
  Frm.of_arrays frameT (by simp [basisSquareRanges])
 exact ⟨basisT,powerT,((first.trans second).trans third).trans fourth,
  (((restA.trans restB).trans restC).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeProduct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeProductIO`, which this module and modules that import it used -/

section

/-! Public subset indices load and store canonical context entries. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/LoadEntry.lean`, which only this module imported.
section

/-! Load an immutable canonical table entry into a native Montgomery operand array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem loadEntry_ok {s : State} {B ctx : Addr} {Z w a j : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31) (array : a<8)
 (context : word s.mem B (8*sCtx)=ctx) (digit : s.gpr .x3=BitVec.ofNat 64 j)
 (readable : ∀ i<w,InRegions (s.rd++s.wr) (off ctx (entryOffset w j+8*i)) 8)
 (outside : ∀ i<8*w,Z≤ofs B (off ctx (entryOffset w j)+BitVec.ofNat 64 i)) :
 WP isa (loadEntry a) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=wv s.mem ctx (entryOffset w j) w ∧
 Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
 have arrHdr : sArr a<32 := by unfold sArr;omega_using [array]
 have arrayRoom : slot w a+8*(w+2)≤Z := Nat.le_trans (slot_le array) room
 unfold loadEntry
 rw [WP.seq_iff,WP.block_append_iff]
 refine WP.mono (entryPtr_ok good room context digit) ?_
 rintro u ⟨⟨ptrU,countU,memU⟩,restU⟩
 refine WP.mono (WP.keep [.x16,.x17] (Q:=fun v =>v.gpr .x16=off ctx (entryOffset w j) ∧
  v.gpr .x17=off B (slot w a) ∧ v.mem=u.mem) ?_ rfl rfl rfl) ?_
 · brun [restU.rd,restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,hdr_enc arrHdr,
    good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot w 8 arrHdr;omega_using [room, this]),memU,good.hdr.harr a array,ptrU]
 · rintro v ⟨⟨srcV,dstV,memV⟩,restV⟩
   have rest := restU.trans restV
   have mem : v.mem=s.mem := memV.trans memU
   refine WP.mono (copyWords_ok (S:=ctx) (D:=B) (eS:=entryOffset w j) (eD:=slot w a) (w:=w) srcV dstV
    ((restV.gpr .x12 (by decide)).trans countU) (by omega_using [positive]) size (by have := good.scr.nowrap;omega_using [arrayRoom, this])
    (fun i hi => by rw [rest.rd,rest.wr];exact readable i hi)
    (fun i hi => by rw [rest.wr];exact good.scr.st (by omega_using [arrayRoom, hi]))
    (fun i hi b hb => Or.inr (by
     have sep := outside (8*i+b) (by omega_using [hi, hb])
     have same : off ctx (entryOffset w j+8*i)+BitVec.ofNat 64 b=
       off ctx (entryOffset w j)+BitVec.ofNat 64 (8*i+b) := by simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
     rw [same]
     omega_using [arrayRoom, sep]))) ?_
   rintro t ⟨value,_,frame,_,_,restT⟩
   have totalRest : Keep mmRegs s t := (rest.trans restT).mono (by simp [mmRegs])
   have arrays : Arrays B w [a] s.mem t.mem := by
    apply Arrays.of_outside (j:=a) (by simp) (o:=slot w a) (n:=8*w)
    · rw [←mem];exact frame
    · omega_using []
    · omega_using []
   refine ⟨good_after_arrays good arrays totalRest ((totalRest.gpr .x0 (by simp [mmRegs])).trans good.x0),?_,arrays,totalRest⟩
   rw [mem] at value
   exact value

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem productLoad_ok {s : State} {p : Parameters} {j : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j) (inside : j<32) :
 WP isa Precompute.productLoad s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.B (slot p.w 1) p.w=wv s.mem p.ctx (entryOffset p.w j) p.w ∧
 Arrays p.B p.w [1] s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.productLoad
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 j ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sJ<32 by decide),header_read good p.room (show sJ<32 by decide),index]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (loadEntry_ok goodU p.room (by have := p.positive;omega_using [this]) p.width (by decide : 1<8)
    (memU ▸ context) indexU
    (fun i hi => (space.after restU).entry_read inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,restT⟩
   rw [memU] at value frame
   exact ⟨goodT,value,frame,(restU.trans restT).mono (by simp [mmRegs])⟩

theorem productStore_ok {s : State} {p : Parameters} {j d : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx)
 (index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j) (basis : word s.mem p.B (8*sD)=BitVec.ofNat 64 d)
 (inside : j+d<32) :
 WP isa Precompute.productStore s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.ctx (entryOffset p.w (j+d)) p.w=wv s.mem p.B (slot p.w 6) p.w ∧
 Outside p.ctx (entryOffset p.w (j+d)) (8*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 unfold Precompute.productStore
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 (j+d) ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
    header_read good p.room (show sJ<32 by decide),header_read good p.room (show sD<32 by decide),index,basis,←BitVec.ofNat_add]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (storeEntry_ok goodU p.room (by have := p.positive;omega_using [this]) p.width (by decide : 6<8)
    (memU ▸ context) indexU (entry_fit p inside)
    (fun i hi => (space.after restU).entry_write inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,unchanged,restT⟩
   rw [memU] at value frame unchanged
   exact ⟨goodT,value,frame,unchanged,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.ProductState`, which this module and modules that import it used -/

section

/-! The invariant for filling the subsets containing one new comb tooth. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BasisProduct.lean`, which only this module imported.
section

/-! Adding one precomputed tooth to an already constructed subset entry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem basis_product (M : Mont) {p : Parameters} {s : State} {E F : Nat} (h : Basis p E s)
 (selected : wv s.mem p.B (slot p.w 1) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 5 1) s fun t =>
 Power p (E+F) t ∧ Basis p E t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound1 : wv s.mem p.B (slot p.w 1) p.w<p.P := by
  rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega_using [this])
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 5<8) (by decide : 1<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound1) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 have mod := h.toModState.after_arrays good frame (by decide) (by decide) (by decide)
 have value := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime bound h.value selected product
 exact ⟨⟨mod,bound,value⟩,h.after_arrays good frame (by decide) (by decide) (by decide) (by decide),frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ProductState (p : Parameters) (b j : Nat) (s : State) : Prop where
 tooth : b<5
 position : 1≤j ∧ j≤2^b
 basis : Basis p (2^(b*Spec.Rsa.FixedBaseComb.rows p.N)) s
 space : ContextSpace p s
 context : word s.mem p.B (8*sCtx)=p.ctx
 basisIndex : word s.mem p.B (8*sD)=BitVec.ofNat 64 (2^b)
 index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j
 table : TablePrefix p (2^b+j) s
 rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)

theorem ProductState.limit {p : Parameters} {b j : Nat} {s : State} (h : ProductState p b j s) : 2^b+j≤32 := by
 have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (show b≤4 by have := h.tooth;omega_using [this])
 have := h.position
 omega_using [bound, this]

theorem ProductState.after_arrays {p : Parameters} {b j : Nat} {s t : State} {js : List Nat}
 (h : ProductState p b j s) (basis : Basis p (2^(b*Spec.Rsa.FixedBaseComb.rows p.N)) t)
 (frame : Arrays p.B p.w js s.mem t.mem) (rest : Keep mmRegs s t) (within : ∀ a∈js,a<8) : ProductState p b j t :=
 ⟨h.tooth,h.position,basis,h.space.after rest,(arrays_header frame (by decide)).trans h.context,
  (arrays_header frame (by decide)).trans h.basisIndex,(arrays_header frame (by decide)).trans h.index,
  h.table.after_inscr h.space h.limit (InScr.of_arrays frame p.room within),
  (arrays_header frame (by decide)).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Construct one new subset entry with the shared Montgomery product. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ProductCounter.lean`, which only this module imported.
section

/-! Advance the public subset index and compare it with the next tooth's table index. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem productCounter_ok {s : State} {B : Addr} {Z w j d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z)
 (index : word s.mem B (8*sJ)=BitVec.ofNat 64 j) (basis : word s.mem B (8*sD)=BitVec.ofNat 64 d) :
 WP isa (.block Precompute.productNext) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*sJ)=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
 Outside B (8*sJ) 8 s.mem t.mem ∧ Keep [.x3,.x4] s t := by
 have increment : BitVec.ofNat 64 j+1#64=BitVec.ofNat 64 (j+1) := (BitVec.ofNat_add _ _).symm
 have frame : Outside B (8*sJ) 8 s.mem (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) :=
  writeW_outside _ _ _ (by decide)
 have basisAfter : word (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) B (8*sD)=BitVec.ofNat 64 d :=
  (frame.word (Or.inl (by decide : 8*sD+8≤8*sJ)) (by decide)).trans basis
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>
  t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
  t.mem=s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) ?_ rfl rfl rfl) ?_
 · unfold Precompute.productNext
   brun [good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
    header_read good room (show sJ<32 by decide),header_read good room (show sD<32 by decide),
    good.scr.st (d:=8*sJ) (by have := hdr_lt_slot w 8 (show sJ<32 by decide);omega_using [room, this]),index,basisAfter,increment]
 · rintro t ⟨⟨value,mem⟩,rest⟩
   have totalFrame : Outside B (8*sJ) 8 s.mem t.mem := by rw [mem];exact frame
   refine ⟨good_after_header good (by decide) (by decide) totalFrame rest ((rest.gpr .x0 (by decide)).trans good.x0),
    ?_,value,totalFrame,rest⟩
   rw [mem,word_writeW_self]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeProduct_ok (M : Mont) {s : State} {p : Parameters} {b j : Nat}
 (h : ProductState p b j s) (more : j<2^b) :
 WP isa (Precompute.product M.mm) s fun t =>
 ProductState p b (j+1) t ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 (2^b) ∧
 BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 have inside : j<32 := by have := h.limit;omega_using [more, this]
 have destination : j+2^b<32 := by
  have tooth := h.tooth
  have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by omega_using [tooth] : b≤4)
  omega_using [more, bound]
 unfold Precompute.product
 rw [WP.seq_iff]
 refine WP.mono (productLoad_ok h.basis.good h.space h.context h.index inside) ?_
 rintro a ⟨goodA,selectedA,frameA,restA⟩
 have basisA := h.basis.after_arrays goodA frameA (by decide) (by decide) (by decide) (by decide)
 have hA := h.after_arrays basisA frameA restA (by simp)
 have selected : wv a.mem p.B (slot p.w 1) p.w=entryValue p j :=
  selectedA.trans (h.table j (by have := h.position;have := Nat.two_pow_pos b;omega_using [more]))
 rw [WP.seq_iff]
 refine WP.mono (basis_product M basisA selected) ?_
 rintro c ⟨powerC,basisC,frameC,restC⟩
 have hC := hA.after_arrays basisC frameC restC (by simp)
 rw [WP.seq_iff]
 refine WP.mono (productStore_ok basisC.good hC.space hC.context hC.index hC.basisIndex destination) ?_
 rintro d ⟨goodD,valueD,frameD,sameD,restD⟩
 have basisD := basisC.after_workspace goodD sameD
 have contextD := (workspace_header basisC.good sameD (by decide : sCtx<32)).trans hC.context
 have indexD := (workspace_header basisC.good sameD (by decide : sJ<32)).trans hC.index
 have rowsD := (workspace_header basisC.good sameD (by decide : sRows<32)).trans hC.rows
 have toothD := (workspace_header basisC.good sameD (by decide : sD<32)).trans hC.basisIndex
 have exponent : 2^(b*Spec.Rsa.FixedBaseComb.rows p.N)+Spec.Rsa.FixedBaseComb.exponent p.N j=
   Spec.Rsa.FixedBaseComb.exponent p.N (2^b+j) := by
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth p.N b j h.tooth more]
  exact Nat.add_comm _ _
 have entry : wv d.mem p.ctx (entryOffset p.w (2^b+j)) p.w=entryValue p (2^b+j) := by
  have value : wv d.mem p.ctx (entryOffset p.w (j+2^b)) p.w=entryValue p (2^b+j) := by
   rw [valueD,powerC.value,exponent]
   rfl
  simpa only [Nat.add_comm j (2^b)] using value
 have tableD : TablePrefix p (2^b+j+1) d := hC.table.extend (by omega_using [destination]) (by
  simpa only [Nat.add_comm j (2^b)] using frameD) entry
 refine WP.mono (productCounter_ok goodD p.room indexD toothD) ?_
 rintro t ⟨goodT,indexT,testT,frameT,restT⟩
 have basisT := basisD.after_header goodT frameT (by decide : sJ<32)
 have tableT := tableD.after_inscr (hC.space.after restD) (by omega_using [destination])
  (InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega_arith))
 have stateT : ProductState p b (j+1) t := by
  refine ⟨h.tooth,⟨by omega_using [],by omega_using [more]⟩,basisT,((hC.space.after restD).after restT),
   (header_other frameT (by decide) (by decide) (by decide)).trans contextD,
   (header_other frameT (by decide) (by decide) (by decide)).trans toothD,indexT,?_,
   (header_other frameT (by decide) (by decide) (by decide)).trans rowsD⟩
  simpa only [Nat.add_assoc] using tableT
 have frames : BuildFrame p s.mem t.mem :=
  (((BuildFrame.of_inscr (InScr.of_arrays frameA p.room (by simp))).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameC p.room (by simp)))).trans
    (BuildFrame.of_entry destination frameD)).trans
    (BuildFrame.of_inscr (InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega_arith)))
 exact ⟨stateT,testT,frames,(((restA.trans restC).trans restD).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeControls`, which this module and modules that import it used -/

section

/-! Fixed public subset initialization and tooth-index advancement. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem setControlNat_ok {s : State} {B : Addr} {Z w i n : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32) (small : n<2^16) :
 WP isa (.block [movi .x3 n,sth .x3 i]) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*i)=BitVec.ofNat 64 n ∧ Outside B (8*i) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off B (8*i)) (BitVec.ofNat 64 n))
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,good.scr.st (d:=8*i) (by have := hdr_lt_slot w 8 upper;omega_using [room, this]),movi_nat small]
 · rintro t ⟨mem,rest⟩
   have frame : Outside B (8*i) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by omega_using [upper])
   refine ⟨good_after_header good lower upper frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem,word_writeW_self]

theorem setControlOne_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32) :
 WP isa (.block [movi .x3 1,sth .x3 i]) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*i)=1#64 ∧ Outside B (8*i) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off B (8*i)) 1#64)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,good.scr.st (d:=8*i) (by have := hdr_lt_slot w 8 upper;omega_using [room, this])]
   rfl
 · rintro t ⟨mem,rest⟩
   have frame : Outside B (8*i) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by omega_using [upper])
   refine ⟨good_after_header good lower upper frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem,word_writeW_self]

theorem basisNext_ok {s : State} {B : Addr} {Z w d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (index : word s.mem B (8*sD)=BitVec.ofNat 64 d) :
 WP isa (.block Precompute.basisNext) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*sD)=BitVec.ofNat 64 (2*d) ∧
 t.gpr .x3=BitVec.ofNat 64 (2*d)-32#64 ∧ Outside B (8*sD) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 have shift : BitVec.ofNat 64 d <<< 1=BitVec.ofNat 64 (2*d) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 d*BitVec.ofNat 64 2=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>
  t.mem=s.mem.writeW (off B (8*sD)) (BitVec.ofNat 64 (2*d)) ∧
  t.gpr .x3=BitVec.ofNat 64 (2*d)-32#64) ?_ rfl rfl rfl) ?_
 · unfold Precompute.basisNext
   brun [good.x0,hdr_enc (show sD<32 by decide),header_read good room (show sD<32 by decide),
    good.scr.st (d:=8*sD) (by have := hdr_lt_slot w 8 (show sD<32 by decide);omega_using [room, this]),index,shift]
 · rintro t ⟨⟨mem,test⟩,rest⟩
   have frame : Outside B (8*sD) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),
    ?_,test,frame,rest⟩
   rw [mem,word_writeW_self]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeProducts`, which only this module used -/

section

/-! Fill all subsets containing the current tooth on a fixed public loop schedule. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

theorem precomputeProducts_ok (M : Mont) {s : State} {p : Parameters} {b : Nat}
 (h : ProductState p b 1 s) (positive : 0<b) :
 WP isa (.loop (Precompute.product M.mm) (.nonzero .x .x3)) s fun t =>
 ProductState p b (2^b) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 obtain bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by have := h.tooth;omega_using [this] : b≤4)
 obtain atLeast : (2:Nat)^1≤2^b := Nat.pow_le_pow_right (by decide) (by omega_using [positive] : 1≤b)
 let I := fun i t => ProductState p b (i+1) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t
 have step (i : Nat) (hi : i<2^b-1) (t : State) (inv : I i t) :
  WP isa (Precompute.product M.mm) t fun u => I (i+1) u ∧ ((u.gpr .x3).toNat≠0 ↔ i+1≠2^b-1) := by
  refine WP.mono (precomputeProduct_ok M inv.1 (by omega_using [hi])) ?_
  rintro u ⟨state,index,frame,rest⟩
  refine ⟨⟨state,inv.2.1.trans frame,(inv.2.2.trans rest).mono (by simp [mmRegs])⟩,?_⟩
  rw [index,BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
   Nat.mod_eq_of_lt (by omega_using [bound, hi] : i+1+1<2^64),Nat.mod_eq_of_lt (by omega_using [bound] : 2^b<2^64)]
  omega_using [bound, hi]
 refine WP.mono (count_loop (by omega_using [atLeast] : 0<2^b-1) I step
  ⟨h,Frame.refl _ _,Keep.refl _ _⟩) ?_
 rintro t ⟨state,frame,rest⟩
 obtain final : 2^b-1+1=2^b := by omega_using [atLeast]
 rw [final] at state
 exact ⟨state,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Build one tooth and all new subsets containing it. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BasisState.lean`, which only this module imported.
section

/-! One public tooth index and the table prefix completed before constructing it. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

structure BasisState (p : Parameters) (b : Nat) (s : State) : Prop where
 tooth : 1≤b ∧ b≤5
 bits : 0<p.N ∧ p.N≤8192
 basis : Basis p (2^((b-1)*Spec.Rsa.FixedBaseComb.rows p.N)) s
 space : ContextSpace p s
 context : word s.mem p.B (8*sCtx)=p.ctx
 index : word s.mem p.B (8*sD)=BitVec.ofNat 64 (2^b)
 rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)
 table : TablePrefix p (2^b) s

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BasisStore.lean`, which only this module imported.
section

/-! Store the next tooth at its public power-of-two index. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem basisStore_ok {s : State} {p : Parameters} {d : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (index : word s.mem p.B (8*sD)=BitVec.ofNat 64 d)
 (inside : d<32) :
 WP isa (.seq (.block [ldh .x3 sD]) (storeEntry 5)) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.ctx (entryOffset p.w d) p.w=wv s.mem p.B (slot p.w 5) p.w ∧
 Outside p.ctx (entryOffset p.w d) (8*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 d ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sD<32 by decide),header_read good p.room (show sD<32 by decide),index]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   obtain goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (storeEntry_ok goodU p.room (by have := p.positive;omega_using [this]) p.width (by decide : 5<8)
    (memU ▸ context) indexU (entry_fit p inside)
    (fun i hi => (space.after restU).entry_write inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,unchanged,restT⟩
   rw [memU] at value frame unchanged
   exact ⟨goodT,value,frame,unchanged,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SquareFrame.lean`, which only this module imported.
section

/-! Squaring changes arithmetic arrays and one counter, preserving the context metadata. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

theorem basisSquareRanges_le (w : Nat) : ∀ r∈basisSquareRanges w,r.1+r.2≤slot w 8 := by
 obtain s2 := slot_le (w:=w) (by decide : 2<8)
 obtain s3 := slot_le (w:=w) (by decide : 3<8)
 obtain s5 := slot_le (w:=w) (by decide : 5<8)
 obtain s6 := slot_le (w:=w) (by decide : 6<8)
 obtain counter := hdr_lt_slot w 8 (show sI<32 by decide)
 simp only [basisSquareRanges,squareRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ ((rfl|rfl|rfl|rfl)|rfl) <;> omega_arith

theorem squareFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (basisSquareRanges w) m m') (inside : i<32) (different : i≠sI) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq ?_ (by omega_using [inside])
 intro r hr
 obtain s2 := hdr_lt_slot w 2 inside
 obtain s3 := hdr_lt_slot w 3 inside
 obtain s5 := hdr_lt_slot w 5 inside
 obtain s6 := hdr_lt_slot w 6 inside
 simp only [basisSquareRanges,squareRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with ((rfl|rfl|rfl|rfl)|rfl) <;> omega_arith

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem regroup {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := ⟨WP.assoc',WP.assoc⟩

theorem precomputeBasis_ok (M : Mont) {s : State} {p : Parameters} {b : Nat}
 (h : BasisState p b s) (more : b<5) :
 WP isa (Precompute.basis M.mm) s fun t =>
 BasisState p (b+1) t ∧ t.gpr .x3=BitVec.ofNat 64 (2^(b+1))-32#64 ∧
 BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 obtain toothBound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by omega_using [more] : b≤4)
 obtain toothPositive : 0<2^b := Nat.two_pow_pos b
 obtain rowsPositive := VG.Proof.Rsa.FixedBaseComb.rows_pos h.bits.1
 obtain rowsBound := (VG.Proof.Rsa.FixedBaseComb.rows_small h.bits.2).1
 unfold Precompute.basis
 rw [WP.seq_iff]
 refine WP.mono (precomputeSquares_ok M h.basis h.rows rowsPositive (by omega_using [rowsBound])) ?_
 rintro a ⟨basisA,_,frameA,restA⟩
 obtain exponent : 2^((b-1)*Spec.Rsa.FixedBaseComb.rows p.N)*2^(Spec.Rsa.FixedBaseComb.rows p.N)=
   2^(b*Spec.Rsa.FixedBaseComb.rows p.N) := by
  rw [←Nat.pow_add]
  congr 1
  calc
   (b-1)*Spec.Rsa.FixedBaseComb.rows p.N+Spec.Rsa.FixedBaseComb.rows p.N=
    (b-1+1)*Spec.Rsa.FixedBaseComb.rows p.N := by ring
   _=b*Spec.Rsa.FixedBaseComb.rows p.N := by rw [Nat.sub_add_cancel h.tooth.1]
 rw [exponent] at basisA
 obtain spaceA := h.space.after restA
 obtain ctxA := (squareFrame_header frameA (by decide : sCtx<32) (by decide)).trans h.context
 obtain indexA := (squareFrame_header frameA (by decide : sD<32) (by decide)).trans h.index
 obtain rowsA := (squareFrame_header frameA (by decide : sRows<32) (by decide)).trans h.rows
 obtain inA := InScr.of_frm frameA (fun r hr => Nat.le_trans (basisSquareRanges_le p.w r hr) p.room)
 obtain tableA := h.table.after_inscr h.space (by omega) inA
 rw [regroup,WP.seq_iff]
 refine WP.mono (basisStore_ok basisA.good spaceA ctxA indexA (by omega)) ?_
 rintro c ⟨goodC,valueC,frameC,sameC,restC⟩
 obtain basisC := basisA.after_workspace goodC sameC
 obtain spaceC := spaceA.after restC
 obtain ctxC := (workspace_header basisA.good sameC (by decide : sCtx<32)).trans ctxA
 obtain indexC := (workspace_header basisA.good sameC (by decide : sD<32)).trans indexA
 obtain rowsC := (workspace_header basisA.good sameC (by decide : sRows<32)).trans rowsA
 obtain entryC : wv c.mem p.ctx (entryOffset p.w (2^b)) p.w=entryValue p (2^b) := by
  unfold entryValue
  rw [valueC,basisA.value,VG.Proof.Rsa.FixedBaseComb.exponent_tooth p.N b more]
 obtain tableC := tableA.extend (by omega_using [toothBound] : 2^b<32) frameC entryC
 rw [WP.seq_iff]
 refine WP.mono (setControlOne_ok goodC p.room (by decide : 16≤sJ) (by decide : sJ<32)) ?_
 rintro d ⟨goodD,oneD,frameD,restD⟩
 obtain inD : InScr p.B p.Z c.mem d.mem := InScr.of_outside frameD (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega_arith)
 obtain tableD := tableC.after_inscr spaceC (by omega) inD
 obtain productD : ProductState p b 1 d :=
  ⟨more,⟨by omega_using [],by omega⟩,basisC.after_header goodD frameD (by decide),spaceC.after restD,
   (header_other frameD (by decide) (by decide) (by decide)).trans ctxC,
   (header_other frameD (by decide) (by decide) (by decide)).trans indexC,oneD,tableD,
   (header_other frameD (by decide) (by decide) (by decide)).trans rowsC⟩
 rw [WP.seq_iff]
 refine WP.mono (precomputeProducts_ok M productD (by have := h.tooth;omega_using [this])) ?_
 rintro e ⟨stateE,frameE,restE⟩
 refine WP.mono (basisNext_ok stateE.basis.good p.room stateE.basisIndex) ?_
 rintro t ⟨goodT,indexT,testT,frameT,restT⟩
 obtain inT : InScr p.B p.Z e.mem t.mem := InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sD<32 by decide);have := p.room;omega_arith)
 obtain tableT := stateE.table.after_inscr stateE.space stateE.limit inT
 obtain nextPower : 2*2^b=2^(b+1) := by rw [Nat.pow_succ];omega_using []
 obtain nextCount : 2^b+2^b=2^(b+1) := by rw [Nat.pow_succ];omega_using []
 obtain stateT : BasisState p (b+1) t := by
  refine ⟨⟨by omega_using [],by omega_using [more]⟩,h.bits,?_,stateE.space.after restT,
   (header_other frameT (by decide) (by decide) (by decide)).trans stateE.context,?_,
   (header_other frameT (by decide) (by decide) (by decide)).trans stateE.rows,?_⟩
  · simpa only [Nat.add_sub_cancel] using stateE.basis.after_header goodT frameT (by decide : sD<32)
  · simpa only [nextPower] using indexT
  · simpa only [nextCount] using tableT
 obtain frames : BuildFrame p s.mem t.mem :=
  ((((BuildFrame.of_inscr inA).trans (BuildFrame.of_entry (by omega_using [toothBound] : 2^b<32) frameC)).trans
    (BuildFrame.of_inscr inD)).trans frameE).trans (BuildFrame.of_inscr inT)
 refine ⟨stateT,?_,frames,((((restA.trans restC).trans restD).trans restE).trans restT).mono (by decide)⟩
 simpa only [nextPower] using testT

end VG.Proof.Ffdh.AArch64.Cached
