module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
public import VerifiedGarbage.Proof.MlDsa.Pack.Written
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec

/-! ### `MlDsa.AArch64.Optimized.KeygenPackWidth`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenPackBody`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenPackTail`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def tailResult (nb : Nat) (m : Mem) (out : Addr) (acc : BitVec 64) : Mem × BitVec 64 :=
  let off := nb/8*8
  let rem := nb%8
  let m1 := if rem≥4 then m.writeW (out+BitVec.ofNat 64 off) (acc.setWidth 32) else m
  let a1 := if rem≥4 then acc>>>32 else acc
  let p := out+BitVec.ofNat 64 (off+rem/4*4)
  let m2 := if rem%4≥2 then (m1.writeW p (a1.setWidth 8)).writeW (p+1) ((a1>>>8).setWidth 8) else m1
  let a2 := if rem%4≥2 then a1>>>16 else a1
  let m3 := if rem%2=1 then m2.writeW (out+BitVec.ofNat 64 (nb-1)) (a2.setWidth 8) else m2
  (m3,a2)

def TailWidth (nb : Nat) : Prop := nb=3 ∨ nb=6 ∨ nb=9 ∨ nb=10 ∨ nb=13

theorem tail_ok (nb : Nat) (hn : TailWidth nb) (s : State)
    (hw : ∀off sz,off+sz≤nb → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz) :
    WP isa (.block (tail nb)) s fun t =>
      ((t.mem=(tailResult nb s.mem (s.gpr .x2) (s.gpr .x9)).1 ∧
        t.gpr .x9=(tailResult nb s.mem (s.gpr .x2) (s.gpr .x9)).2) ∧
       Keep [.x9] s t) ∧ t.v=s.v := by
  rcases hn with rfl|rfl|rfl|rfl|rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 : InRegions s.wr (s.gpr .x2) 1 := by simpa using hw 0 1 (by decide)
    have h1 := hw 1 1 (by decide)
    have h2 := hw 2 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,h2,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 : InRegions s.wr (s.gpr .x2) 4 := by simpa using hw 0 4 (by decide)
    have h1 := hw 4 1 (by decide)
    have h2 := hw 5 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,h2,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 1 (by decide)
    have h1 := hw 9 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl
  · apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
    have h0 := hw 8 4 (by decide)
    have h1 := hw 12 1 (by decide)
    dsimp only [tail,tailResult]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    arun [exec,addr,State.store,State.read,Size.bytes,Option.bind_some,h0,h1,Mem.writeW,BitVec.add_assoc,←BitVec.shiftRight_add]
    all_goals rfl


end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackLoads`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.KeygenPackLoad`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

structure Constants (b : Nat) (s : State) : Prop where
  bias : ∀e<4,vword (s.v .v16) e=BitVec.ofNat 32 b
  modulus : ∀e<4,vword (s.v .v17) e=8380417#32

theorem Constants.chg {b : Nat} {s t : State} {rs : List VReg}
    (h : Constants b s) (k : VChg rs s t) (h16 : VReg.v16∉rs) (h17 : VReg.v17∉rs) :
    Constants b t := ⟨by rw [k.get _ h16]; exact h.bias,by rw [k.get _ h17]; exact h.modulus⟩

theorem loadOne_ok (signed : Bool) (b : Nat) {r : VReg}
    (hr : r∉[VReg.v4,.v16,.v17]) {s : State} (hc : signed=true → Constants b s)
    {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [r,.v4] s t → (signed=true → Constants b t) →
      (∀e<4,vword (t.v r) e=if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e)
        else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e) → WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq r .x0 off :: ((if signed then convert r else [])++rest))) s Q := by
  have h16 : VReg.v16≠r := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact Ne.symm hr.2.1
  have h17 : VReg.v17≠r := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact Ne.symm hr.2.2
  refine wp_ldrq ho rfl hin fun a ha => ?_
  cases signed with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,List.nil_append]
    exact k a (ha.chg.mono (by simp)) (by simp) (by intro e he; rw [ha.v]; rfl)
  | true =>
    simp only [↓reduceIte]
    have ca := (hc rfl).chg ha.chg (by simpa using h16) (by simpa using h17)
    refine convert_ok r hr b ca.bias ca.modulus fun t ht hv => ?_
    have hk : VChg [r,.v4] s t := (ha.chg.trans ht).mono (by simp)
    refine k t hk (fun _=>(hc rfl).chg hk (by simp [h16]) (by simp [h17])) ?_
    intro e he
    rw [hv e he,ha.v]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def regAt (j : Nat) : VReg := if j=0 then .v0 else if j=1 then .v1 else if j=2 then .v2 else .v3

theorem regAt_small {j : Nat} : regAt j∈[VReg.v0,.v1,.v2,.v3] := by
  unfold regAt
  (repeat' split) <;> simp

theorem regAt_reserved {j : Nat} : regAt j∉[VReg.v4,.v16,.v17] := by
  unfold regAt
  (repeat' split) <;> decide

theorem regAt_distinct {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) : regAt i≠regAt j := by
  dsimp only [regAt]
  (repeat' split) <;> first | decide | omega

def loadCode (signed : Bool) (j : Nat) : List Instr :=
  .ldrq (regAt j) .x0 (16*j) :: (if signed then convert (regAt j) else [])

theorem loadCount_ok (signed : Bool) (b count : Nat) (hn : count≤4) (s : State)
    (hc : signed=true → Constants b s)
    (hin : ∀j<count,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block ((List.range count).flatMap (loadCode signed))) s fun t =>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
      ∀j<count,∀e<4,vword (t.v (regAt j)) e=
        if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
        else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e := by
  let I := fun n t=>VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
    ∀j<n,∀e<4,vword (t.v (regAt j)) e=
      if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht=>?_) count (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hct,hvals⟩
    rw [loadCode,←List.append_nil (if signed then convert (regAt j) else [])]
    refine loadOne_ok signed b regAt_reserved hct ⟨by omega_using [],by omega_using [hn, hj]⟩ ?_ fun u hu hcu hv => WP.block_nil_iff.mpr ?_
    · simpa only [hk.rd,hk.wr,hk.gpr] using hin j hj
    · refine ⟨(hk.trans hu).mono ?_,hcu,?_⟩
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with hr|rfl|rfl
        · simpa using hr
        · exact List.mem_append_left [.v4] regAt_small
        · simp
      · intro i hi e he
        by_cases hij : i=j
        · subst i
          rw [hv e he,hk.mem,hk.gpr]
        · have hi' : i<j := by omega_using [hi, hij]
          rw [hu.get (regAt i) (by simp [regAt_distinct (by omega_using [hn, hj, hi]) (by omega_using [hn, hj]) hij,
            show regAt i≠VReg.v4 by have := regAt_reserved (j:=i); simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at this; exact this.1])]
          exact hvals i hi' e he
  · exact ⟨VChg.refl _ _,hc,by intro j hj; omega⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackStreamMemory`, which only this module used -/

section

/-! ## From `KeygenPackStream.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.Pack

def acc64 (G d j : Nat) : Nat := G%2^(d*j)/2^(64*(d*j/64))

theorem acc64_lt (G d j : Nat) : acc64 G d j<2^(d*j%64) := by
  have h := mod_div_lt G (d*j) (64*(d*j/64))
  simpa only [acc64,show d*j-64*(d*j/64)=d*j%64 by omega_using []] using h

theorem add64 (G d j : Nat) :
    acc64 G d j+(G/2^(d*j)%2^d)*2^(d*j%64)=
      G%2^(d*(j+1))/2^(64*(d*j/64)) := by
  unfold acc64
  rw [Nat.mul_succ,mod_two_pow_add,two_pow_split (show 64*(d*j/64)≤d*j by omega_using []),
    show d*j-64*(d*j/64)=d*j%64 by omega_using [],Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.mul_comm (2^(d*j%64))]

theorem ofNat_shift (v sh : Nat) :
    (BitVec.ofNat 64 v<<<sh)=BitVec.ofNat 64 (v*2^sh) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]

theorem joined_nat (d j a v : Nat) (ha : a<2^(d*j%64)) :
    joined d j (BitVec.ofNat 64 a) (BitVec.ofNat 64 v)=
      BitVec.ofNat 64 (a+v*2^(d*j%64)) := by
  unfold joined
  split
  · rename_i h
    have hz : a=0 := by simpa only [h,Nat.pow_zero,Nat.lt_one_iff] using ha
    simp only [hz,h,Nat.pow_zero,Nat.mul_one,Nat.zero_add]
  · rw [ofNat_shift,←BitVec.ofNat_or,Nat.or_comm,
      Nat.mul_comm v,←Nat.two_pow_add_eq_or_of_lt ha v,Nat.add_comm]

theorem joined_acc (G d j : Nat) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G%2^(d*(j+1))/2^(64*(d*j/64))) := by
  rw [joined_nat _ _ _ _ (acc64_lt G d j),add64]

theorem joined_flush {G d j : Nat} (h : 64≤d*j%64+d) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G/2^(64*(d*j/64))) := by
  rw [joined_acc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact VG.Proof.MlKem.mod_pow_div_mod G (by rw [Nat.mul_succ]; omega_using [h])

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackCarry.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

theorem digit_tail (G a d c : Nat) :
    (G/2^a%2^d)/2^c=G%2^(a+d)/2^(a+c) := by
  rw [Nat.pow_add 2 a c,←Nat.div_div_eq_div_mul,Nat.pow_add 2 a d,Nat.mod_mul_right_div_self]

theorem digit_lt64 (G d j : Nat) (hd : d≤20) : G/2^(d*j)%2^d<2^64 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) (by omega_using [hd]))

theorem acc64_lt64 (G d j : Nat) : acc64 G d j<2^64 :=
  Nat.lt_of_lt_of_le (acc64_lt G d j)
    (Nat.pow_le_pow_right (by decide) (by omega_using []))

theorem fieldAcc_next (G d j : Nat) (hd : d≤20) (hn : d*(j+1)%64≠0) :
    fieldAcc d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (acc64 G d (j+1)) := by
  have ha : d*(j+1)=d*j+d := Nat.mul_succ _ _
  by_cases hc : 64<d*j%64+d
  · rw [fieldAcc,ite_eq_left hc]
    have hb : 64*(d*(j+1)/64)=d*j+(64-d*j%64) := by rw [ha]; omega_using [hd, hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (digit_lt64 G d j hd),BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (acc64_lt64 G d (j+1))]
    rw [digit_tail,acc64,hb,ha]
  · rw [fieldAcc,ite_eq_right hc,joined_acc]
    have hb : d*(j+1)/64=d*j/64 := by rw [ha] at hn ⊢; omega_using [hn, hc]
    rw [acc64,hb]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackStreamMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

def byteOf (G j : Nat) : Byte := BitVec.ofNat 8 (G/2^(8*j))

theorem word_byte (G k : Nat) {j : Nat} (hj : j<8) :
    (BitVec.ofNat 64 (G/2^(8*k))).extractLsb' (8*j) 8=byteOf G (k+j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    VG.Proof.MlKem.mod_pow_div_mod _ (by omega_using [hj]),Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]
  rfl

theorem joined_congr (d j : Nat) (a b v : BitVec 64) (h : d*j%64≠0 → a=b) :
    joined d j a v=joined d j b v := by
  by_cases hz : d*j%64=0
  · simp only [joined,hz,↓reduceIte]
  · rw [h hz]

theorem fieldAcc_congr (d j : Nat) (a b v : BitVec 64) (h : d*j%64≠0 → a=b) :
    fieldAcc d j a v=fieldAcc d j b v := by
  unfold fieldAcc
  rw [joined_congr d j a b v h]

theorem fields_written (G d : Nat) (hd : d≤20) (m : Mem) (out : Addr) (a : BitVec 64)
    {n : Nat} (hn : n≤8) :
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ n
    Written m f.mem out (8*(d*n/64)) (byteOf G) ∧
      (d*n%64≠0 → f.acc=BitVec.ofNat 64 (acc64 G d n)) := by
  induction n with
  | zero =>
    simpa only [fieldsRun,Nat.mul_zero,Nat.zero_div,Nat.zero_mod,ne_eq,not_true_eq_false,false_implies,and_true] using Written.nil m out (byteOf G)
  | succ n ih =>
    obtain ⟨hw,ha⟩ := ih (by omega_using [hn])
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ n
    have hj : joined d n f.acc (BitVec.ofNat 64 (G/2^(d*n)%2^d))=
        joined d n (BitVec.ofNat 64 (acc64 G d n)) (BitVec.ofNat 64 (G/2^(d*n)%2^d)) :=
      joined_congr d n _ _ _ ha
    constructor
    · by_cases hf : 64≤d*n%64+d
      · have hb : 8*(d*(n+1)/64)=8*(d*n/64)+8 := by rw [Nat.mul_succ]; omega_using [hd, hf]
        change Written m (fieldMem d n f.mem out f.acc _) out _ _
        rw [fieldMem,ite_eq_left hf,hj,joined_flush hf,hb,
          show 64*(d*n/64)=8*(8*(d*n/64)) by omega_using []]
        apply written_append hw ?_ (by have := Nat.mul_le_mul hd (show n≤8 by omega_using [hn]); omega_using [this])
        simpa only [Nat.mul_comm] using (written_word f.mem (out+BitVec.ofNat 64 (d*n/64*8)) 8
          (BitVec.ofNat 64 (G/2^(8*(8*(d*n/64)))))).congr (fun j hj=>word_byte G _ hj)
      · have hb : d*(n+1)/64=d*n/64 := by rw [Nat.mul_succ]; omega_using [hf]
        change Written m (fieldMem d n f.mem out f.acc _) out _ _
        rw [fieldMem,ite_eq_right hf,hb]
        exact hw
    · intro hnext
      change fieldAcc d n f.acc _= _
      rw [fieldAcc_congr d n f.acc (BitVec.ofNat 64 (acc64 G d n)) _ ha]
      exact fieldAcc_next G d n hd hnext

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackInput`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def inputValue (signed : Bool) (b : Nat) (m : Mem) (p : Addr) (j : Nat) : BitVec 64 :=
  (if signed then encoded b (coeffAt m p j) else coeffAt m p j).setWidth 64

theorem inputWord (m : Mem) (p : Addr) (j : Nat) :
    vword (m.read (p+BitVec.ofNat 64 (16*(j/4))) 16) (j%4)=coeffAt m p j := by
  rw [VG.AArch64.vword_read16 _ _ (by omega_using []),BitVec.add_assoc,←BitVec.ofNat_add,
    show 16*(j/4)+4*(j%4)=4*j by omega_using []]
  rfl

theorem loadVec_ok (signed : Bool) (b c : Nat) (hc : c≤8) (hc4 : c%4=0) (s : State)
    (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.block (loadVec signed c)) s fun t =>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
      ∀j<c,fieldValue t.v j=inputValue signed b s.mem (s.gpr .x0) j := by
  have hcode : loadVec signed c=(List.range (c/4)).flatMap (loadCode signed) := by
    unfold loadVec
    congr 1
  rw [hcode]
  refine WP.mono (loadCount_ok signed b (c/4) (by omega_using [hc]) s hconst ?_) fun t ⟨hk,hct,hv⟩ => ?_
  · intro j hj
    exact hin _ (by omega_using [hj])
  · refine ⟨hk,hct,?_⟩
    intro j hj
    have hreg : regAt (j/4)=(if j<4 then VReg.v0 else .v1) := by
      unfold regAt
      (repeat' split) <;> first | rfl | omega
    have h := hv (j/4) (by omega_using [hc4, hj]) (j%4) (by omega_using [])
    rw [hreg,inputWord] at h
    exact congrArg (BitVec.setWidth 64) h

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

/-! ## From `KeygenPackTailMemory.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/KeygenPackGroup.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def groupCode (signed : Bool) (_b d c : Nat) : List Instr :=
  loadVec signed c ++ (List.range c).flatMap (field d) ++ tail (d*c/8)

def groupResult (signed : Bool) (b d c : Nat) (m : Mem) (input out : Addr) : Mem × BitVec 64 :=
  let f := fieldsRun d out (inputValue signed b m input) ⟨m,0⟩ c
  tailResult (d*c/8) f.mem out f.acc

theorem group_ok (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : 0<c) (hc8 : c≤8) (hc4 : c%4=0)
    (hn : TailWidth (d*c/8)) (s : State) (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hout : ∀off sz,off+sz≤d*c/8 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz) :
    WP isa (.block (groupCode signed b d c)) s fun t =>
      Keep [.x9,.x10,.x11] s t ∧ (signed=true → Constants b t) ∧
      t.mem=(groupResult signed b d c s.mem (s.gpr .x0) (s.gpr .x2)).1 ∧
      t.gpr .x9=(groupResult signed b d c s.mem (s.gpr .x0) (s.gpr .x2)).2 := by
  simp only [groupCode,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadVec_ok signed b c hc8 hc4 s hconst hin) fun a ⟨ha,ca,hvalues⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fields_ok d c hd hc8 a ?_) fun f ⟨hf,hfv,hfm,hfa⟩ => ?_
  · intro off ho
    simpa only [ha.wr,ha.gpr] using hout off 8 ho
  · have he : fieldsRun d (a.gpr .x2) (fieldValue a.v) ⟨a.mem,a.gpr .x9⟩ c=
        fieldsRun d (s.gpr .x2) (inputValue signed b s.mem (s.gpr .x0)) ⟨s.mem,0⟩ c := by
      rw [ha.gpr,ha.mem,fieldsRun_values d (s.gpr .x2) _ _ _ hvalues]
      exact fieldsRun_acc_irrel d hd _ _ _ _ _ hc
    rw [he] at hfm hfa
    refine WP.mono (tail_ok (d*c/8) hn f ?_) fun t ⟨⟨⟨htm,hta⟩,ht⟩,htv⟩ => ?_
    · intro off sz ho
      simpa only [hf.wr,ha.wr,hf.get .x2,ha.gpr] using hout off sz ho
    · refine ⟨((ha.keep.trans hf).trans ht).mono,?_,?_,?_⟩
      · intro h
        have hh := ca h
        exact ⟨by rw [htv,hfv]; exact hh.bias,by rw [htv,hfv]; exact hh.modulus⟩
      · rw [htm,hfm,hfa,hf.get .x2,ha.gpr]
        rfl
      · rw [hta,hfm,hfa,hf.get .x2,ha.gpr]
        rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/KeygenPackAdvance.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def advance (d c : Nat) : List Instr :=
  [.addImm .x .x0 .x0 (4*c),.addImm .x .x2 .x2 (d*c/8),.subImm .x .x15 .x15 1]

theorem advance_ok (d c : Nat) (hd : d≤20) (hc : c≤8) (s : State) :
    WP isa (.block (advance d c)) s fun t =>
      ((t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (4*c) ∧
        t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (d*c/8) ∧
        t.gpr .x15=s.gpr .x15-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x15] s t) ∧ t.v=s.v := by
  have hh := Nat.mul_le_mul hd hc
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  have h4 : 4*c<4096 := by omega_using [hc]
  have h8 : d*c/8<4096 := by omega_using [hh]
  arun [exec,h4,h8]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

theorem slice_word (G base sh w : Nat) (h : sh+w≤64) :
    ((BitVec.ofNat 64 (G/2^base))>>>sh).setWidth w=BitVec.ofNat w (G/2^(base+sh)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow,VG.Proof.MlKem.mod_pow_div_mod _ h,
    Nat.div_div_eq_div_mul,←Nat.pow_add,BitVec.toNat_ofNat]

theorem smallWord_byte (G k n : Nat) {j : Nat} (hj : j<n) :
    (BitVec.ofNat (8*n) (G/2^(8*k))).extractLsb' (8*j) 8=byteOf G (k+j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    VG.Proof.MlKem.mod_pow_div_mod _ (by omega_using [hj]),Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]
  rfl

theorem written_small (G k n : Nat) (m : Mem) (out : Addr) :
    Written m (m.writeW out (BitVec.ofNat (8*n) (G/2^(8*k)))) out n (fun j=>byteOf G (k+j)) :=
  (written_word m out n _).congr fun _j hj=>smallWord_byte G k n hj


theorem slice_zero (G sh w : Nat) (h : sh+w≤64) :
    ((BitVec.ofNat 64 G)>>>sh).setWidth w=BitVec.ofNat w (G/2^sh) := by
  simpa only [Nat.pow_zero,Nat.div_one,Nat.zero_add] using slice_word G 0 sh w h

theorem tail_written (nb G : Nat) (hn : TailWidth nb) (m : Mem) (out : Addr) :
    Written m (tailResult nb m out (BitVec.ofNat 64 G)).1
      (out+BitVec.ofNat 64 (nb/8*8)) (nb%8) (byteOf G) := by
  rcases hn with rfl|rfl|rfl|rfl|rfl
  · simp [tailResult]
    rw [slice_zero G 8 8 (by decide),slice_zero G 16 8 (by decide)]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 0)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 1 1 ((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 8 G)) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 1)
    have p1 := written_append h0 h1 (by decide)
    have h2 := written_small G 2 1 (((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 8 G)).writeW ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 1) (BitVec.ofNat 8 (G/2^8))) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 2)
    have p2 := written_append p1 h2 (by decide)
    simpa only [BitVec.add_assoc,BitVec.add_zero] using p2
  · simp [tailResult, BitVec.add_assoc, ←BitVec.shiftRight_add]
    rw [slice_zero G 32 8 (by decide),slice_zero G 40 8 (by decide)]
    have h0 := written_small G 0 4 (m) (out+BitVec.ofNat 64 0)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 4 1 ((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 32 G)) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 4)
    have p1 := written_append h0 h1 (by decide)
    have h2 := written_small G 5 1 (((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 32 G)).writeW ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 4) (BitVec.ofNat 8 (G/2^32))) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 5)
    have p2 := written_append p1 h2 (by decide)
    simpa only [BitVec.add_assoc,BitVec.add_zero] using p2
  · simp [tailResult]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    simpa only [BitVec.add_assoc,BitVec.add_zero] using h0
  · simp [tailResult, BitVec.add_assoc]
    rw [slice_zero G 8 8 (by decide)]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 1 1 ((m).writeW (out+BitVec.ofNat 64 8) (BitVec.ofNat 8 G)) ((out+BitVec.ofNat 64 8)+BitVec.ofNat 64 1)
    have p1 := written_append h0 h1 (by decide)
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using p1
  · simp [tailResult]
    rw [slice_zero G 32 8 (by decide)]
    have h0 := written_small G 0 4 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 4 1 ((m).writeW (out+BitVec.ofNat 64 8) (BitVec.ofNat 32 G)) ((out+BitVec.ofNat 64 8)+BitVec.ofNat 64 4)
    have p1 := written_append h0 h1 (by decide)
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using p1

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackGroupMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

theorem byteOf_div (G k j : Nat) : byteOf (G/2^(8*k)) j=byteOf G (k+j) := by
  unfold byteOf
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]

theorem stream_written (G d c : Nat) (hd : d≤20) (hc : c≤8)
    (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (hG : G<2^(d*c))
    (m : Mem) (out : Addr) (a : BitVec 64) :
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ c
    Written m (tailResult (d*c/8) f.mem out f.acc).1 out (d*c/8) (byteOf G) := by
  dsimp only
  obtain ⟨hw,ha⟩ := fields_written G d hd m out a hc
  have hnz : d*c%64≠0 := by rcases ht with h|h|h|h|h <;> omega
  have hdiv : d*c/8/8=d*c/64 := by omega_using []
  have hacc : acc64 G d c=G/2^(8*(d*c/8/8*8)) := by
    rw [acc64,Nat.mod_eq_of_lt hG,hdiv]
    congr 2
    omega_using []
  rw [ha hnz,hacc]
  have htail := tail_written (d*c/8) (G/2^(8*(d*c/8/8*8))) ht
    (fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ c).mem out
  have htail' := htail.congr fun j _=>byteOf_div G (d*c/8/8*8) j
  have hbase : d*c/8/8*8=8*(d*c/64) := by omega_using []
  rw [hbase] at htail'
  have hlength : 8*(d*c/64)+d*c/8%8=d*c/8 := by omega_using []
  have hh := written_append hw htail' (by have := Nat.mul_le_mul hd hc; omega_using [this])
  simpa only [hlength,hbase] using hh

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackGroupBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)

theorem group_written (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : c≤8)
    (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (m : Mem) (input out : Addr)
    (V : Nat → Nat) (hV : ∀j<c,V j<2^d)
    (hin : ∀j<c,inputValue signed b m input j=BitVec.ofNat 64 (V j)) :
    Written m (groupResult signed b d c m input out).1 out (d*c/8)
      (byteOf (digits d ((List.range c).map V))) := by
  let G := digits d ((List.range c).map V)
  have hf := fieldsRun_values d out (inputValue signed b m input)
    (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,0⟩ (fun j hj=>by
      rw [hin j hj,digits_range_get hV hj])
  unfold groupResult
  rw [hf]
  exact stream_written G d c hd hc halign ht (digits_range_lt hV) m out 0

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

def fieldValueNat (signed : Bool) (b : Nat) (x : BitVec 32) : Nat :=
  if signed then VG.Proof.MlDsa.AArch64.Pack.bpVal b x else x.toNat

theorem inputValue_nat (signed : Bool) (b : Nat) (m : Mem) (input : Addr) (j : Nat)
    (hb : b<q) (hx : (coeffAt m input j).toNat<q) :
    inputValue signed b m input j=BitVec.ofNat 64 (fieldValueNat signed b (coeffAt m input j)) := by
  cases signed
  · simp [inputValue,fieldValueNat]
  · simp only [inputValue,fieldValueNat,↓reduceIte]
    rw [show (encoded b (coeffAt m input j)).setWidth 64=
      BitVec.ofNat 64 (encoded b (coeffAt m input j)).toNat by simp,
      encoded_bpVal hb hx]

theorem inputValue_shift (signed : Bool) (b : Nat) (m : Mem) (input : Addr) (k j : Nat) :
    inputValue signed b m (input+BitVec.ofNat 64 (4*k)) j=inputValue signed b m input (k+j) := by
  unfold inputValue coeffAt
  rw [BitVec.add_assoc,←BitVec.ofNat_add,←Nat.mul_add]

theorem inputValue_frame (signed : Bool) (b : Nat) {m t : Mem} {input : Addr}
    {rs : List Region} (h : Frame rs m t)
    (hs : ∀r∈rs,(polyRegion input).Disjoint r) {j : Nat} (hj : j<256) :
    inputValue signed b t input j=inputValue signed b m input j := by
  unfold inputValue
  rw [coeffAt_frame h hs hj]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlKem (digits)

abbrev widthRegs : List Reg := [.x0,.x2,.x9,.x10,.x11,.x15]
def widthBody (signed : Bool) (b d c : Nat) : List Instr := groupCode signed b d c ++ advance d c

theorem body_ok (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : 0<c) (hc8 : c≤8)
    (hc4 : c%4=0) (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (s : State)
    (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hout : ∀off sz,off+sz≤d*c/8 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz)
    (V : Nat → Nat) (hV : ∀j<c,V j<2^d)
    (hvalues : ∀j<c,inputValue signed b s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j)) :
    WP isa (.block (widthBody signed b d c)) s fun t=>
      Written s.mem t.mem (s.gpr .x2) (d*c/8) (byteOf (digits d ((List.range c).map V))) ∧
      t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (4*c) ∧
      t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (d*c/8) ∧
      t.gpr .x15=s.gpr .x15-1 ∧ Keep widthRegs s t ∧ (signed=true → Constants b t) := by
  rw [widthBody,WP.block_append_iff]
  refine WP.mono (group_ok signed b d c hd hc hc8 hc4 ht s hconst hin hout) fun a ⟨hk,ha,hm,_⟩=>?_
  refine WP.mono (advance_ok d c hd hc8 a) fun t ⟨⟨⟨h0,h2,h15,htm⟩,kt⟩,hv⟩=>?_
  refine ⟨?_,?_,?_,?_,(hk.trans kt).mono,?_⟩
  · rw [htm,hm]
    exact group_written signed b d c hd hc8 halign ht s.mem (s.gpr .x0) (s.gpr .x2) V hV hvalues
  · rw [h0,hk.get .x0]
  · rw [h2,hk.get .x2]
  · rw [h15,hk.get .x15]
  · intro hh
    have hh' := ha hh
    exact ⟨by rw [hv];exact hh'.bias,by rw [hv];exact hh'.modulus⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

/-! ## From `KeygenPackSetup.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (Keep wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord repeatedWord_lane)

theorem vc_ok (s : State) (d : VReg) (n : Nat) :
    WP isa (.block (vc d n)) s fun t=>ConstKeep d s t ∧ t.v d=repeatedWord n := by
  rw [vc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 (BitVec.ofNat 64 n)) fun a ha=>?_
  refine wp_vop (d:=d) rfl fun t ht=>WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr=>?_,fun r hr=>?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,ha.2.2]
    · rw [ht.mem,ha.2.2]
    · rw [ht.rd,ha.2.2]
    · rw [ht.wr,ha.2.2]
    · rw [ht.sp,ha.2.2]
  · rw [ht.v,ha.1]
    simp [repeatedWord]

theorem constants_ok (s : State) (b : Nat) :
    WP isa (.block (vc .v16 b ++ vc .v17 8380417)) s fun t=>
      SetupKeep [.v16,.v17] s t ∧ Constants b t := by
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok s .v16 b) fun a ha=>?_
  refine WP.mono (vc_ok a .v17 8380417) fun t ht=>?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem setup_ok (signed : Bool) (b : Nat) (s : State) :
    WP isa (.block (setup signed b)) s fun t=>
      Keep [.x2,.x9] s t ∧ t.mem=s.mem ∧
      t.gpr .x2=(if signed then s.gpr .x3 else s.gpr .x2) ∧
      (signed=true → Constants b t) := by
  cases signed
  · exact WP.block_nil_iff.mpr ⟨Keep.refl _ _,rfl,rfl,by simp⟩
  · simp only [setup,↓reduceIte,List.cons_append,List.nil_append]
    refine VG.Proof.MlKem.AArch64.wp_mov fun a ha h2=>?_
    refine WP.mono (constants_ok a b) fun t ⟨ht,hc⟩=>?_
    refine ⟨?_,ht.mem.trans ha.mem,?_,fun _=>hc⟩
    · exact ⟨fun r hr=>by rw [ht.gpr r (by simp_all),ha.gpr r (by simp_all)],
        ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,fun r hr=>by
          rw [ht.vec r (by rcases r <;> simp_all [preservedV])];exact ha.vcs r hr⟩
    · rw [ht.gpr .x2 (by decide),h2]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackWidthLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape)
open VG.Proof.MlKem.AArch64 (Keep ptr_add)
open VG.Proof.MlKem (digits)

structure WidthInv (signed : Bool) (b d c : Nat) (m : Mem) (input out : Addr)
    (B : Nat → Byte) (start : State) (i : Nat) (s : State) : Prop where
  input : s.gpr .x0=input+BitVec.ofNat 64 (4*c*i)
  output : s.gpr .x2=out+BitVec.ofNat 64 (d*c/8*i)
  bytes : ∀j<d*c/8*i,s.mem (out+BitVec.ofNat 64 j)=B j
  frame : Frame [⟨out,32*d⟩] m s.mem
  keep : Keep widthRegs start s
  constants : signed=true → Constants b s

section
variable (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
  (ht : TailWidth (d*c/8)) (start : State) (input out : Addr) (V : Nat → Nat) (B : Nat → Byte)
  (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,32*d⟩:Region)∈start.wr)
  (hsep : (polyRegion input).Disjoint ⟨out,32*d⟩)
  (hv : ∀j<256,V j<2^d)
  (hvalues : ∀j<256,inputValue signed b start.mem input j=BitVec.ofNat 64 (V j))
  (hbytes : ∀i<256/c,∀j<d*c/8,
    byteOf (digits d ((List.range c).map fun k=>V (c*i+k))) j=B (d*c/8*i+j))
include hs hc4 ht hin hout hsep hv hvalues hbytes

theorem width_step {i : Nat} (hi : i<256/c) {s : State}
    (h : WidthInv signed b d c start.mem input out B start i s) :
    WP isa (.block (widthBody signed b d c)) s fun t=>
      WidthInv signed b d c start.mem input out B start (i+1) t ∧ t.gpr .x15=s.gpr .x15-1 := by
  obtain ⟨hci,hbi⟩ := hs.group hi
  have hpoly : 4*c*i+4*c≤1024 := by simpa only [Nat.mul_add,Nat.mul_assoc] using Nat.mul_le_mul_left 4 hci
  have hn : 32*d<2^64 := by have := hs.d20;omega_arith
  have hg : d*c%8=0 := by have := hs.dc;omega_arith
  refine WP.mono (body_ok signed b d c hs.d20 hs.c0 hs.c8 hc4 hg ht s h.constants ?_ ?_
    (fun j=>V (c*i+j)) (fun j hj=>hv _ (by omega_arith)) ?_) fun t ⟨hw,h0,h2,h15,hk,hc⟩=>?_
  · intro off hoff
    rw [h.input,ptr_add,h.keep.rd,h.keep.wr]
    exact ⟨_,hin,Offset.contains_base input (by omega_arith) (by omega_arith)⟩
  · intro off sz hoff
    rw [h.output,ptr_add,h.keep.wr]
    exact ⟨_,hout,Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  · intro j hj
    have hij : c*i+j<256 := by omega_arith
    rw [h.input,show 4*c*i=4*(c*i) by rw [Nat.mul_assoc],inputValue_shift,
      inputValue_frame signed b h.frame (by intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hsep) hij]
    exact hvalues _ (by omega_arith)
  · have hw' := hw.congr (hbytes i hi)
    rw [h.output] at hw'
    obtain ⟨hf,hb⟩ := Written.step h.frame h.bytes hw' hbi hn
    refine ⟨⟨?_,?_,?_,hf,(h.keep.trans hk).mono,hc⟩,h15⟩
    · rw [h0,h.input,ptr_add,Nat.mul_succ]
    · rw [h2,h.output,ptr_add,Nat.mul_succ]
    · simpa only [Nat.mul_succ] using hb

theorem width_loop {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants b s) (h15 : s.gpr .x15=BitVec.ofNat 64 (256/c)) :
    WP isa (.loop (.block (widthBody signed b d c)) (.nonzero .x .x15)) s fun t=>
      (∀j<32*d,t.mem (out+BitVec.ofNat 64 j)=B j) ∧
      Frame [⟨out,32*d⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  obtain ⟨hN0,hN⟩ := hs.G
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.wp_countdown (by omega_arith) hN0
    (WidthInv signed b d c start.mem input out B start)
    (fun i hi s h _=>width_step signed b d c hs hc4 ht start input out V B hin hout hsep hv hvalues hbytes hi h)
    (s:=s) ?_ h15) fun t h=>?_
  · exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
      by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h2,
      by intro j hj;simp only [Nat.mul_zero] at hj;omega_arith,
      by rw [hm];exact Frame.refl _ _,hk,hc⟩
  · exact ⟨by simpa only [hs.bN] using h.bytes,h.frame,h.keep⟩

end
end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackWidthBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (d c : Nat) (hs : Shape d c (d*c/8)) (hV : ∀j<256,F (coeffAt m input j)<2^d)
    {i j : Nat} (hi : i<256/c) (hj : j<d*c/8) :
    byteOf (digits d ((List.range c).map fun k=>F (coeffAt m input (c*i+k)))) j=
      (bitsToBytes (fieldBits d (vals F m input)))[d*c/8*i+j]! := by
  obtain ⟨hc,hb⟩ := hs.group hi
  rw [pack_group (c:=c) (by have := hs.d1;omega_arith) hs.dc (by simp) (vals_lt hV) hj (by omega_arith),
    take_drop_eq _ 0 (by simp;omega_arith)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits d L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega_arith)

theorem width_loop_bytes (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (start : State) (input out : Addr) (F : BitVec 32 → Nat)
    (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,32*d⟩:Region)∈start.wr)
    (hsep : (polyRegion input).Disjoint ⟨out,32*d⟩)
    (hv : ∀j<256,F (coeffAt start.mem input j)<2^d)
    (hvalues : ∀j<256,inputValue signed b start.mem input j=BitVec.ofNat 64 (F (coeffAt start.mem input j)))
    {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants b s) (h15 : s.gpr .x15=BitVec.ofNat 64 (256/c)) :
    WP isa (.loop (.block (widthBody signed b d c)) (.nonzero .x .x15)) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem out (32*d)=bitsToBytes (fieldBits d (vals F start.mem input)) ∧
      Frame [⟨out,32*d⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  refine WP.mono (width_loop signed b d c hs hc4 ht start input out
    (fun j=>F (coeffAt start.mem input j))
    (fun j=>(bitsToBytes (fieldBits d (vals F start.mem input)))[j]!)
    hin hout hsep hv hvalues (fun i hi j hj=>packed_group F start.mem input d c hs hv hi hj)
    h0 h2 hm hk hc h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length d _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackWidth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem counter_ok (n : Nat) (hn : n<2^16) (s : State) :
    WP isa (.block [.movz .x .x15 (BitVec.ofNat 16 n) 0]) s fun t=>
      ((t.gpr .x15=BitVec.ofNat 64 n ∧ t.mem=s.mem) ∧ Keep [.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]

theorem width_ok (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<2^d)
    (hvalues : ∀j<256,inputValue signed b s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (width signed b d c) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) (32*d)=
        bitsToBytes (fieldBits d (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  unfold width
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (setup_ok signed b s) fun a ⟨ka,ma,oa,ca⟩=>?_
  refine WP.mono (counter_ok (256/c) (by have := hs.G;omega_arith) a) fun u ⟨⟨⟨cu,mu⟩,ku⟩,vu⟩=>?_
  have hk : Keep widthRegs s u := (ka.trans ku).mono
  exact width_loop_bytes signed b d c hs hc4 ht s (s.gpr .x0)
    (if signed then s.gpr .x3 else s.gpr .x2) F hin hout hsep hv hvalues
    (by rw [ku.get .x0,ka.get .x0]) (by rw [ku.get .x2,oa]) (mu.trans ma) hk
    (fun h=>⟨by rw [vu];exact (ca h).bias,by rw [vu];exact (ca h).modulus⟩) cu

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackFourGroup`, which only this module used -/

section

/-! ## From `KeygenPackFourInput.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

theorem four_low_byte (x : BitVec 128) (e : Nat) :
    vbyte x (4*e)=(vword x e).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [vbyte,vword,hk,show k<32 by omega_using [hk]]
  congr 1
  omega_using []

theorem four_table_word (v : VReg → BitVec 128) {i : Nat} (hi : i<16) :
    tableByte v .v0 (4*i)=(vword (v (regAt (i/4))) (i%4)).setWidth 8 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega_using [hi]) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v0) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v1) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v2) 3
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 0
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 1
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 2
  · simpa [tableByte,regAt,Nat.repeat,VReg.succ] using four_low_byte (v .v3) 3

theorem four_table_nibbles (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀j<4,∀e<4,vword (v (regAt j)) e=(f (4*j+e)).setWidth 32) :
    ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8 := by
  intro i hi
  rw [four_table_word v hi,h _ (by omega_using [hi]) _ (by omega_using []),show 4*(i/4)+i%4=i by omega_using []]
  simp

theorem fourLoadShuffle_ok (signed : Bool) (s : State) (f : Nat → BitVec 4)
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hv : ∀j<4,∀e<4,(if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=(f (4*j+e)).setWidth 32)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.KeygenPack.loadVec signed 16++fourShuffle)) s fun t=>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧
      ∀i<8,vbyte (t.v .v0) i=(f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  rw [WP.block_append_iff]
  refine WP.mono (loadCount_ok signed 4 4 (by decide) s hc hin) fun a ⟨ha,_,hwa⟩=>?_
  rw [←List.append_nil fourShuffle]
  refine fourShuffle_bytes f (by rw [ha.get .v18 (by decide)];exact hg)
    (by rw [ha.get .v19 (by decide)];exact hp)
    (by rw [ha.get .v20 (by decide)];exact hm)
    (four_table_nibbles a.v f (fun j hj e he=>(hwa j hj e he).trans (hv j hj e he)))
    fun t ht hb=>WP.block_nil_iff.mpr ⟨(ha.trans ht).mono (by simp),hb⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourStore_ok (s : State) (hw : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block [.umov .x .x9 .v0 0,.str .x .x9 .x2 0]) s fun t=>
      ((t.gpr .x9=(s.v .v0).extractLsb' 0 64 ∧
        t.mem=s.mem.writeW (s.gpr .x2) ((s.v .v0).extractLsb' 0 64)) ∧ Keep [.x9] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=by rfl)
  arun [Option.bind_some,exec,addr,Size.bytes,State.store,State.read,Mem.writeW,hw]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def fourGroup (signed : Bool) : List Instr :=
  Impl.MlDsa.AArch64.Optimized.KeygenPack.loadVec signed 16++fourShuffle++
    [.umov .x .x9 .v0 0,.str .x .x9 .x2 0]

theorem fourStored_byte (x : BitVec 128) {i : Nat} (hi : i<8) :
    (x.extractLsb' 0 64).extractLsb' (8*i) 8=vbyte x i := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte,BitVec.getLsbD_extractLsb',hk,show 8*i+k<64 by omega_using [hi, hk],
    decide_true,Bool.true_and,Nat.zero_add]

theorem fourGroup_ok (signed : Bool) (s : State) (f : Nat → BitVec 4)
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hv : ∀j<4,∀e<4,(if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=(f (4*j+e)).setWidth 32)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourGroup signed)) s fun t=>
      Keep [.x9] s t ∧
      (∀r,r∉[VReg.v0,.v1,.v2,.v3,.v4] → t.v r=s.v r) ∧
      t.mem=s.mem.writeW (s.gpr .x2) (t.gpr .x9) ∧
      ∀i<8,(t.gpr .x9).extractLsb' (8*i) 8=
        (f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  unfold fourGroup
  rw [WP.block_append_iff]
  refine WP.mono (fourLoadShuffle_ok signed s f hc hin hv hg hp hm) fun a ⟨ha,hbytes⟩=>?_
  refine WP.mono (fourStore_ok a (by simpa only [ha.wr,ha.gpr] using hout)) fun t ⟨⟨⟨hword,hmem⟩,ht⟩,htv⟩=>?_
  refine ⟨(ha.keep.trans ht).mono,?_,?_,?_⟩
  · intro r hr
    rw [htv,ha.get r hr]
  · rw [hmem,ha.mem,ha.gpr,hword]
  · intro i hi
    rw [hword,fourStored_byte _ hi]
    exact hbytes i hi

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackFourSetup`, which only this module used -/

section

/-! ## From `KeygenPackFourConst.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)

structure FourTableKeep (d : VReg) (s t : State) : Prop where
  gpr : ∀r,r≠.x9 → r≠.x10 → t.gpr r=s.gpr r
  vec : ∀r,r≠d → t.v r=s.v r
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

def fourTableValue (xs : List Nat) : BitVec 128 :=
  ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl (fun v i=>v+xs[i]!*2^(8*i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun v i=>v+xs[8+i]!*2^(8*i)) 0))

theorem fourTable_ok (s : State) (d : VReg) (xs : List Nat) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.KeygenPack.tblc d xs)) s fun t=>
      FourTableKeep d s t ∧ t.v d=fourTableValue xs := by
  unfold Impl.MlDsa.AArch64.Optimized.KeygenPack.tblc
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 _) fun a ha=>?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok a .x10 _) fun b hb=>?_
  refine wp_vop (d:=d) rfl fun c hc=>wp_vop (d:=d) rfl fun t ht=>WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r h9 h10=>?_,fun r hr=>?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hc.gpr,hb.2.1 r h10,ha.2.1 r h9]
    · rw [ht.other r hr,hc.other r hr,hb.2.2,ha.2.2]
    · rw [ht.mem,hc.mem,hb.2.2,ha.2.2]
    · rw [ht.rd,hc.rd,hb.2.2,ha.2.2]
    · rw [ht.wr,hc.wr,hb.2.2,ha.2.2]
    · rw [ht.sp,hc.sp,hb.2.2,ha.2.2]
  · rw [ht.v,hc.gpr,hb.1,hc.v,hb.2.1 .x9 (by decide),ha.1]
    exact setLane_pair_hi _ _ _

theorem fourGatherTable_value :
    fourTableValue [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]=fourGatherIndex := by
  decide +kernel

theorem fourPackTable_value :
    fourTableValue [0,1,4,5,8,9,12,13,255,255,255,255,255,255,255,255]=fourPackIndex := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (repeatedWord_lane)

theorem FourTableKeep.keep {d : VReg} {s t : State} (h : FourTableKeep d s t)
    (hd : d∉preservedV) : Keep [.x9,.x10] s t := by
  refine ⟨fun r hr=>h.gpr r (by simp_all) (by simp_all),h.rd,h.wr,h.sp,?_⟩
  intro r hr
  rw [h.vec r (by intro he;subst r;exact hd hr)]

def fourSetup (signed : Bool) : List Instr :=
  setup signed 4 ++
  tblc .v18 [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60] ++
  tblc .v19 [0,1,4,5,8,9,12,13,255,255,255,255,255,255,255,255] ++
  vc .v20 0x00ff00ff ++ [.movz .x .x15 16 0]

theorem fourSetup_ok (signed : Bool) (s : State) :
    WP isa (.block (fourSetup signed)) s fun t=>
      Keep [.x2,.x9,.x10,.x15] s t ∧ t.mem=s.mem ∧
      t.gpr .x2=(if signed then s.gpr .x3 else s.gpr .x2) ∧
      (signed=true → Constants 4 t) ∧ t.v .v18=fourGatherIndex ∧
      t.v .v19=fourPackIndex ∧ (∀e<4,vword (t.v .v20) e=0x00ff00ff) ∧ t.gpr .x15=16 := by
  unfold fourSetup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setup_ok signed 4 s) fun a ⟨ka,ma,oa,ca⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (fourTable_ok a .v18 _) fun b ⟨kb,hb⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (fourTable_ok b .v19 _) fun c ⟨kc,hc⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok c .v20 _) fun d ⟨kd,hd⟩=>?_
  refine WP.mono (counter_ok 16 (by decide) d) fun t ⟨⟨⟨ht,mt⟩,kt⟩,vt⟩=>?_
  have kk : Keep [.x9] c d := ⟨fun r hr=>kd.gpr r (by simpa using hr),kd.rd,kd.wr,kd.sp,
    fun r hr=>by rw [kd.vec r (by rcases r <;> simp_all [preservedV])]⟩
  refine ⟨((((ka.trans (kb.keep (by decide))).trans (kc.keep (by decide))).trans kk).trans kt).mono,
    mt.trans (kd.mem.trans (kc.mem.trans (kb.mem.trans ma))),?_,?_,?_,?_,?_,ht⟩
  · rw [kt.get .x2,kd.gpr .x2 (by decide),kc.gpr .x2 (by decide) (by decide),
      kb.gpr .x2 (by decide) (by decide),oa]
  · intro h
    exact ⟨by rw [vt,kd.vec .v16 (by decide),kc.vec .v16 (by decide),kb.vec .v16 (by decide)];exact (ca h).bias,
      by rw [vt,kd.vec .v17 (by decide),kc.vec .v17 (by decide),kb.vec .v17 (by decide)];exact (ca h).modulus⟩
  · rw [vt,kd.vec .v18 (by decide),kc.vec .v18 (by decide),hb,fourGatherTable_value]
  · rw [vt,kd.vec .v19 (by decide),hc,fourPackTable_value]
  · intro e he
    rw [vt,hd,repeatedWord_lane _ he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end


/-! ## From `KeygenPackFourAdvance.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourAdvance_ok (s : State) :
    WP isa (.block (advance 4 16)) s fun t =>
      ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x2=s.gpr .x2+8 ∧
        t.gpr .x15=s.gpr .x15-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun [advance]
  exact ⟨rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourCanonical.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)

theorem nibble_pair (a b : Nat) (ha : a<16) (hb : b<16) :
    (BitVec.ofNat 4 a).setWidth 8 ||| ((BitVec.ofNat 4 b).setWidth 8<<<4)=
      BitVec.ofNat 8 (a+16*b) := by
  have hA : (BitVec.ofNat 4 a).setWidth 8=BitVec.ofNat 8 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt ha]
  have hB : (BitVec.ofNat 4 b).setWidth 8=BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt hb]
  rw [hA,hB]
  have hshift : (BitVec.ofNat 8 b<<<4)=BitVec.ofNat 8 (16*b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]
    rw [Nat.mul_comm b]
  rw [hshift,←BitVec.ofNat_or,Nat.or_comm,←Nat.two_pow_add_eq_or_of_lt (show a<2^4 from ha) b,Nat.add_comm]

theorem four_byte (V : Nat → Nat) (hV : ∀j<16,V j<16) {i : Nat} (hi : i<8) :
    byteOf (digits 4 ((List.range 16).map V)) i=
      (BitVec.ofNat 4 (V (2*i))).setWidth 8 ||| ((BitVec.ofNat 4 (V (2*i+1))).setWidth 8<<<4) := by
  rw [nibble_pair _ _ (hV _ (by omega_arith)) (hV _ (by omega_arith))]
  let G := digits 4 ((List.range 16).map V)
  have h0 := digits_range_get (d:=4) (c:=16) hV (show 2*i<16 by omega_arith)
  have h1 := digits_range_get (d:=4) (c:=16) hV (show 2*i+1<16 by omega_arith)
  change G/2^(4*(2*i))%16=V (2*i) at h0
  change G/2^(4*(2*i+1))%16=V (2*i+1) at h1
  apply BitVec.eq_of_toNat_eq
  change (G/2^(8*i))%256=(V (2*i)+16*V (2*i+1))%256
  have hsum : V (2*i)+16*V (2*i+1)<256 := by have := hV (2*i) (by omega_arith);have := hV (2*i+1) (by omega_arith);omega_arith
  rw [Nat.mod_eq_of_lt hsum,show 256=16*16 by decide,Nat.mod_mul]
  rw [show 8*i=4*(2*i) by omega_arith,h0]
  congr 1
  rw [show 16=2^4 by decide,Nat.div_div_eq_div_mul,←Nat.pow_add,
    show 4*(2*i)+4=4*(2*i+1) by omega_arith]
  exact congrArg (16*·) h1

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourWritten.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)
open VG.Proof.MlKem.AArch64 (Keep)

theorem four_input (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    {j e : Nat} (hj : j<4) (he : e<4) :
    (if signed then encoded 4 (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)=
      (BitVec.ofNat 4 (V (4*j+e))).setWidth 32 := by
  have h := congrArg (BitVec.setWidth 32) (hvalues (4*j+e) (by omega_arith))
  simp only [inputValue,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq] at h
  have hw := inputWord s.mem (s.gpr .x0) (4*j+e)
  rw [show (4*j+e)/4=j by omega_arith,show (4*j+e)%4=e by omega_arith] at hw
  rw [hw,h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,
    show 2^4=16 by decide]
  have hv := hV (4*j+e) (by omega_arith)
  omega_arith

theorem fourGroup_written (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourGroup signed)) s fun t=>
      Keep [.x9] s t ∧ (∀r,r∉[VReg.v0,.v1,.v2,.v3,.v4] → t.v r=s.v r) ∧
      Written s.mem t.mem (s.gpr .x2) 8 (byteOf (digits 4 ((List.range 16).map V))) := by
  refine WP.mono (fourGroup_ok signed s (fun j=>BitVec.ofNat 4 (V j)) hc hin
    (fun j hj e he=>four_input signed s V hV hvalues hj he) hg hp hm hout) fun t ⟨hk,hv,hmem,hbytes⟩=>?_
  refine ⟨hk,hv,?_⟩
  rw [hmem]
  exact (written_word s.mem (s.gpr .x2) 8 (t.gpr .x9)).congr fun i hi=>
    (hbytes i hi).trans (four_byte V hV hi).symm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlKem (digits)

def fourBody (signed : Bool) : List Instr := fourGroup signed ++ advance 4 16

theorem fourBody_ok (signed : Bool) (s : State) (V : Nat → Nat) (hV : ∀j<16,V j<16)
    (hvalues : ∀j<16,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (V j))
    (hc : signed=true → Constants 4 s)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hout : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block (fourBody signed)) s fun t=>
      Written s.mem t.mem (s.gpr .x2) 8 (byteOf (digits 4 ((List.range 16).map V))) ∧
      t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x2=s.gpr .x2+8 ∧
      t.gpr .x15=s.gpr .x15-1 ∧ Keep widthRegs s t ∧
      (signed=true → Constants 4 t) ∧ t.v .v18=fourGatherIndex ∧
      t.v .v19=fourPackIndex ∧ (∀e<4,vword (t.v .v20) e=0x00ff00ff) := by
  rw [fourBody,WP.block_append_iff]
  refine WP.mono (fourGroup_written signed s V hV hvalues hc hin hg hp hm hout) fun a ⟨hk,hv,hw⟩=>?_
  refine WP.mono (fourAdvance_ok a) fun t ⟨⟨⟨h0,h2,h15,htm⟩,kt⟩,vt⟩=>?_
  refine ⟨by rw [htm];exact hw,?_,?_,?_,(hk.trans kt).mono,?_,?_,?_,?_⟩
  · rw [h0,hk.get .x0]
  · rw [h2,hk.get .x2]
  · rw [h15,hk.get .x15]
  · intro hh
    exact ⟨by rw [vt,hv .v16 (by decide)];exact (hc hh).bias,
      by rw [vt,hv .v17 (by decide)];exact (hc hh).modulus⟩
  · rw [vt,hv .v18 (by decide),hg]
  · rw [vt,hv .v19 (by decide),hp]
  · rw [vt,hv .v20 (by decide)];exact hm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Keep ptr_add)
open VG.Proof.MlKem (digits)

structure FourInv (signed : Bool) (m : Mem) (input out : Addr)
    (B : Nat → Byte) (start : State) (i : Nat) (s : State) : Prop where
  input : s.gpr .x0=input+BitVec.ofNat 64 (64*i)
  output : s.gpr .x2=out+BitVec.ofNat 64 (8*i)
  bytes : ∀j<8*i,s.mem (out+BitVec.ofNat 64 j)=B j
  frame : Frame [⟨out,128⟩] m s.mem
  keep : Keep widthRegs start s
  constants : signed=true → Constants 4 s
  gather : s.v .v18=fourGatherIndex
  pack : s.v .v19=fourPackIndex
  mask : ∀e<4,vword (s.v .v20) e=0x00ff00ff

section
variable (signed : Bool) (start : State) (input out : Addr) (V : Nat → Nat) (B : Nat → Byte)
  (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,128⟩:Region)∈start.wr)
  (hsep : (polyRegion input).Disjoint ⟨out,128⟩)
  (hv : ∀j<256,V j<16)
  (hvalues : ∀j<256,inputValue signed 4 start.mem input j=BitVec.ofNat 64 (V j))
  (hbytes : ∀i<16,∀j<8,
    byteOf (digits 4 ((List.range 16).map fun k=>V (16*i+k))) j=B (8*i+j))
include hin hout hsep hv hvalues hbytes

theorem four_step {i : Nat} (hi : i<16) {s : State}
    (h : FourInv signed start.mem input out B start i s) :
    WP isa (.block (fourBody signed)) s fun t=>
      FourInv signed start.mem input out B start (i+1) t ∧ t.gpr .x15=s.gpr .x15-1 := by
  refine WP.mono (fourBody_ok signed s (fun j=>V (16*i+j)) (fun j hj=>hv _ (by omega_arith)) ?_
    h.constants ?_ h.gather h.pack h.mask ?_) fun t ⟨hw,h0,h2,h15,hk,hc,hg,hp,hm⟩=>?_
  · intro j hj
    rw [h.input,show 64*i=4*(16*i) by omega_arith,inputValue_shift,
      inputValue_frame signed 4 h.frame (by intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hsep) (by omega_arith)]
    exact hvalues _ (by omega_arith)
  · intro j hj
    rw [h.input,ptr_add,h.keep.rd,h.keep.wr]
    exact ⟨_,hin,Offset.contains_base input (by omega_arith) (by omega_arith)⟩
  · rw [h.output,h.keep.wr]
    exact ⟨_,hout,Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  · have hw' := hw.congr (hbytes i hi)
    rw [h.output] at hw'
    obtain ⟨hf,hb⟩ := Written.step h.frame h.bytes hw' (by omega_arith) (by decide : 128<2^64)
    refine ⟨⟨?_,?_,?_,hf,(h.keep.trans hk).mono,hc,hg,hp,hm⟩,h15⟩
    · rw [h0,h.input,show (64:BitVec 64)=BitVec.ofNat 64 64 by rfl,ptr_add,Nat.mul_succ]
    · rw [h2,h.output,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
    · simpa only [Nat.mul_succ] using hb

theorem four_loop {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants 4 s) (hg : s.v .v18=fourGatherIndex)
    (hp : s.v .v19=fourPackIndex) (hmask : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (h15 : s.gpr .x15=16) :
    WP isa (.loop (.block (fourBody signed)) (.nonzero .x .x15)) s fun t=>
      (∀j<128,t.mem (out+BitVec.ofNat 64 j)=B j) ∧
      Frame [⟨out,128⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=16) (by decide) (by decide)
    (FourInv signed start.mem input out B start)
    (fun i hi s h _=>four_step signed start input out V B hin hout hsep hv hvalues hbytes hi h)
    (s:=s) ?_ h15) fun t h=>⟨h.bytes,h.frame,h.keep⟩
  exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
    by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h2,
    by intro j hj;simp only [Nat.mul_zero] at hj;omega_arith,
    by rw [hm];exact Frame.refl _ _,hk,hc,hg,hp,hmask⟩

end
end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem four_packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (hV : ∀j<256,F (coeffAt m input j)<16) {i j : Nat} (hi : i<16) (hj : j<8) :
    byteOf (digits 4 ((List.range 16).map fun k=>F (coeffAt m input (16*i+k)))) j=
      (bitsToBytes (fieldBits 4 (vals F m input)))[8*i+j]! := by
  rw [pack_group (c:=16) (by decide : 0<4) (by decide : 4*16=8*8) (by simp)
    (vals_lt hV) hj (by omega_arith),take_drop_eq _ 0 (by simp;omega_arith)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits 4 L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega_arith)

theorem four_ok (signed : Bool) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<16)
    (hvalues : ∀j<256,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) 128=
        bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  have hcode : Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed=
      .seq (.block (fourSetup signed)) (.loop (.block (fourBody signed)) (.nonzero .x .x15)) := by
    simp [Impl.MlDsa.AArch64.Optimized.KeygenPack.four,fourSetup,fourBody,fourGroup,fourShuffle,advance,List.append_assoc]
  rw [hcode]
  refine WP.seq ?_
  refine WP.mono (fourSetup_ok signed s) fun u ⟨hk,hm,h2,hc,hg,hp,hmask,h15⟩=>?_
  refine WP.mono (four_loop signed s (s.gpr .x0) (if signed then s.gpr .x3 else s.gpr .x2)
    (fun j=>F (coeffAt s.mem (s.gpr .x0) j))
    (fun j=>(bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))))[j]!) hin hout hsep hv hvalues
    (fun i hi j hj=>four_packed_group F s.mem (s.gpr .x0) hv hi hj)
    (hk.get .x0) h2 hm hk.mono hc hg hp hmask h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length 4 _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourContracts.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only)

theorem simple_four_wp {s₀ s : State} (hp : simpleBitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x3).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four false) s
      (fun t=>simpleBitPackK.post s₀ t) := by
  have hcases := sbp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1)=4 := by omega_arith
  obtain ⟨hrd,hwr,hsep,hb,hlen,hle⟩ := hp
  rw [hd] at hlen
  refine WP.mono (four_ok false s BitVec.toNat ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x2,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x2,hlen,Bool.false_eq_true,↓reduceIte] using hsep
  · intro i hi
    change (coeffAt s.mem (s.gpr .x0) i).toNat<2^4
    rw [ho.mem,ho.get .x0,←hd]
    exact lt_bitlen (hle i hi)
  · intro i _
    simp [inputValue]
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat=simpleBitPack _ _
    simp only [Bool.false_eq_true,↓reduceIte,ho.get .x2,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,simpleBitPack_eq,natPolyAt_toList,hd]

theorem signed_four_wp {s₀ s : State} (hp : bitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x4).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four true) s
      (fun t=>bitPackK.post s₀ t) := by
  have hcases := bp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1+wArg s₀ .x2)=4 := by omega_arith
  have hB : wArg s₀ .x2=4 := by omega_arith
  obtain ⟨hrd,hwr,hsep,hab,hlen,hred,hbnd⟩ := hp
  have hc := bp_cases hab hlen
  have hq : q=8380417 := rfl
  rw [hd] at hlen
  refine WP.mono (four_ok true s (bpVal 4) ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x3,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x3,hlen,↓reduceIte] using hsep
  · intro i hi
    change bpVal 4 (coeffAt s.mem (s.gpr .x0) i)<2^4
    rw [ho.mem,ho.get .x0]
    obtain ⟨h₁,h₂⟩ := hbnd i hi
    rw [hB] at h₂
    have hx := hred i hi
    rw [bpVal,←BitVec.ofNat_toNat,subModQ_toNat (by omega_arith) hx,
      ←sub_modPm hx (by omega_arith) h₂]
    have hh := lt_bitlen (sub_modPm_le h₁ h₂)
    simpa only [show bitlen (wArg s₀ .x1+4)=4 by simpa only [hB] using hd] using hh
  · intro i hi
    simpa only [fieldValueNat,↓reduceIte] using inputValue_nat true 4 s.mem (s.gpr .x0) i
      (by omega_arith) (by rw [ho.mem,ho.get .x0];exact hred i hi)
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat=bitPack _ _ _
    simp only [↓reduceIte,ho.get .x3,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,bitPack_eq,bitPack_vals hred (by omega_arith) (fun i hi=>(hbnd i hi).2),hd,hB]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end
