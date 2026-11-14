module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
public import VerifiedGarbage.Proof.MlDsa.Pack.Written
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoads
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackTail
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
