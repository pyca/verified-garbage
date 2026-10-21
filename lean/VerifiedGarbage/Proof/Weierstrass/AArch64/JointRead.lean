module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNaf9
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-! The generator's digit `j` as the joint loop reads it, for either width: its byte (the low byte
of its sixteen-bit word for width nine), its table index, and its sign (the word's high byte). -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- The generator's digit `j` as `Joint.fixedRead` leaves it in `x2`. -/
def jointGCell (c : Joint.Cfg) (u j : Nat) : BitVec 64 :=
  if c.gw=9 then (FastNaf.wbyte u (2*j)).setWidth 64 else (FastNaf.byte 7 u j).setWidth 64

/-- The offset of digit `j`'s first byte past `c.gBits`. -/
def jointGPos (c : Joint.Cfg) (j : Nat) : Nat := if c.gw=9 then 2*j else j

theorem wbyte_lo_toNat (u j : Nat) : (FastNaf.wbyte u (2*j)).toNat=
    if FastNaf.negative 9 u j then 256-FastNaf.magnitude 9 u j else FastNaf.magnitude 9 u j := by
  rw [fastWbyte_toNat,fastWord9_toNat,show 2*j/2=j by omega,show 2*j%2=0 by omega]
  have hb := fastMagnitude_bound 9 u j
  cases hn : FastNaf.negative 9 u j
  · simp only [Bool.false_eq_true,ite_false] <;> omega
  · have hp := FastNaf.negative_magnitude_pos 9 u j hn
    simp only [ite_true] <;> omega

theorem wbyte_hi_toNat (u j : Nat) : (FastNaf.wbyte u (2*j+1)).toNat=
    if FastNaf.negative 9 u j then 255 else 0 := by
  rw [fastWbyte_toNat,fastWord9_toNat,show (2*j+1)/2=j by omega,show (2*j+1)%2=1 by omega]
  have hb := fastMagnitude_bound 9 u j
  cases hn : FastNaf.negative 9 u j
  · simp only [Bool.false_eq_true,ite_false] <;> omega
  · have hp := FastNaf.negative_magnitude_pos 9 u j hn
    simp only [ite_true] <;> omega

theorem setWidth64_zero_iff : ∀ x : BitVec 8,x.setWidth 64=0 ↔ x.toNat=0 := by decide +kernel

theorem jointGCell_zero_iff {c : Joint.Cfg} (hg : c.gw=7 ∨ c.gw=9) (u j : Nat) :
    jointGCell c u j=0 ↔ FastNaf.magnitude c.gw u j=0 := by
  by_cases h9 : c.gw=9
  · rw [jointGCell,ite_eq_left h9,h9,setWidth64_zero_iff,wbyte_lo_toNat]
    have hb := fastMagnitude_bound 9 u j
    cases hn : FastNaf.negative 9 u j
    · simp only [Bool.false_eq_true,ite_false]
    · have hp := FastNaf.negative_magnitude_pos 9 u j hn
      simp only [ite_true]; omega
  · have h7 := hg.resolve_right h9
    rw [jointGCell,ite_eq_right h9,h7,←FastNaf.byte_zero_iff 7 u j,setWidth64_zero_iff,
      ←BitVec.toNat_inj]
    rfl

/-- `x2` = the byte at `bits + 2 x19`, and `x16` = `x0 + 2 x19`. -/
theorem nafRead2_ok {s : State} {base : Addr} {size bits j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hb : bits<4096) (hj : bits+2*j<size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (hm : s.mem (off base (bits+2*j))=b) (r : Reg)
    (hr16 : r≠.x16) :
    WP isa (.block [.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb r .x16 bits]) s fun t =>
      t.gpr r=b.setWidth 64 ∧ t.gpr .x16=off base (2*j) ∧ Keeps [r,.x16] s t := by
  have hrr : InRegions (s.rd++s.wr) (off base (bits+2*j)) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have h2 : base+BitVec.ofNat 64 j+BitVec.ofNat 64 j=off base (2*j) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show j+j=2*j by omega]
  have he : off base (2*j)+BitVec.ofNat 64 bits=off base (bits+2*j) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [Nat.add_comm (2*j)]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
    RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,
    hs.x0,h19,Size.bits,Nat.mod_one,hb,and_self,reduceCtorEq,ite_false,h2,he,hrr,
    ite_true,read1_zext,hm,Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,?_,?_,rfl,rfl,rfl,rfl⟩
  · simp only [Ne.symm hr16,ite_false]
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,hq.1,hq.2,ite_false]

/-- `r` = the byte at `bits + x19`, and `x16` = `x0 + x19`. -/
theorem nafRead1_ok {s : State} {base : Addr} {size bits j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hb : bits<4096) (hj : bits+j<size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (hm : s.mem (off base (bits+j))=b) (r : Reg)
    (hr16 : r≠.x16) :
    WP isa (.block [.add .x .x16 .x0 .x19,.ldrb r .x16 bits]) s fun t =>
      t.gpr r=b.setWidth 64 ∧ t.gpr .x16=off base j ∧ Keeps [r,.x16] s t := by
  have hrr : InRegions (s.rd++s.wr) (off base (bits+j)) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have he : base+BitVec.ofNat 64 j+BitVec.ofNat 64 bits=off base (bits+j) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [Nat.add_comm j]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
    RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,
    hs.x0,h19,Size.bits,Nat.mod_one,hb,and_self,he,hrr,
    ite_true,read1_zext,hm,Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,?_,?_,rfl,rfl,rfl,rfl⟩
  · simp only [Ne.symm hr16,ite_false]
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,hq.1,hq.2,ite_false]

/-- `x16 = x0 + 2 x19`. -/
theorem nafAdd2_ok {s : State} {base : Addr} {size j : Nat} (hs : Scr s base size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block [.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19]) s fun t =>
      t.gpr .x16=off base (2*j) ∧ Keeps [.x16] s t := by
  have h2 : base+BitVec.ofNat 64 j+BitVec.ofNat 64 j=off base (2*j) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show j+j=2*j by omega]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,hs.x0,h19,reduceCtorEq,ite_false,ite_true,h2,
    Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,rfl,rfl,rfl,rfl⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_write,hq,ite_false]

/-- `x3` = the byte at `bits + 1` past `x16 = x0 + 2 j`. -/
theorem nafHiByte_ok {s : State} {base : Addr} {size bits j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hb : bits+1<4096) (hj : bits+2*j+1<size)
    (h16 : s.gpr .x16=off base (2*j)) (hm : s.mem (off base (bits+(2*j+1)))=b) :
    WP isa (.block [.ldrb .x3 .x16 (bits+1)]) s fun t =>
      t.gpr .x3=b.setWidth 64 ∧ Keeps [.x3] s t := by
  have hrr : InRegions (s.rd++s.wr) (off base (bits+(2*j+1))) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have he : off base (2*j)+BitVec.ofNat 64 (bits+1)=off base (bits+(2*j+1)) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 2*j+(bits+1)=bits+(2*j+1) by omega]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.load,addr,
    RegUpd.gpr_write,h16,Size.bits,Nat.mod_one,hb,and_self,he,hrr,
    ite_true,read1_zext,hm,Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,rfl,rfl,rfl,rfl⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_write,hq,ite_false]

/-- The generator's digit `j`'s byte, where it is, and for width nine its high byte. -/
theorem jointFixedRead_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hB : c.gBits+1<4096)
    (hj : j<257) (hl : c.gBits+jointGLen c≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hm : ∀ i<jointGLen c,s.mem (off base (c.gBits+i))=jointGByte c u i) :
    WP isa (.block (Joint.fixedRead c)) s fun t =>
      t.gpr .x2=jointGCell c u j ∧ t.gpr .x16=off base (jointGPos c j) ∧
      (c.gw=9 → t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64) ∧ Keeps [.x2,.x3,.x16] s t := by
  by_cases h9 : c.gw=9
  · have hlen : jointGLen c=514 := by rw [jointGLen,ite_eq_left h9]
    have g := hm (2*j) (by omega)
    have g1 := hm (2*j+1) (by omega)
    rw [jointGByte,ite_eq_left h9] at g g1
    rw [Joint.fixedRead,ite_eq_left h9,
      show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x2 .x16 c.gBits,
        .ldrb .x3 .x16 (c.gBits+1)] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,
        .ldrb .x2 .x16 c.gBits]++[.ldrb .x3 .x16 (c.gBits+1)] from rfl,WP.block_append_iff]
    refine WP.mono (nafRead2_ok hs (by omega) (by omega) h19 g .x2 (by decide)) fun a ⟨a2,a16,ka⟩ => ?_
    refine WP.mono (nafHiByte_ok (hs.of_keeps ka (by decide)) hB (by omega) a16 (by rw [ka.mem]; exact g1))
      fun t ⟨t3,kt⟩ => ⟨?_,?_,fun _ => t3,(ka.mono (by simp)).trans (kt.mono (by simp))⟩
    · rw [kt.gpr _ (by decide),a2,jointGCell,ite_eq_left h9]
    · rw [kt.gpr _ (by decide),a16,jointGPos,ite_eq_left h9]
  · have hlen : jointGLen c=257 := by rw [jointGLen,ite_eq_right h9]
    have g := hm j (by omega)
    rw [jointGByte,ite_eq_right h9] at g
    rw [Joint.fixedRead,ite_eq_right h9]
    refine WP.mono (nafRead1_ok hs (by omega) (by omega) h19 g .x2 (by decide)) fun t ⟨t2,t16,kt⟩ =>
      ⟨?_,?_,fun h => absurd h h9,kt.mono (by simp)⟩
    · rw [t2,jointGCell,ite_eq_right h9]
    · rw [t16,jointGPos,ite_eq_right h9]

theorem fixedIndexW_fact : ∀ L : BitVec 8,∀ b : Bool,
    let x : BitVec 64 := L.setWidth 64
    let sign : BitVec 64 := BitVec.ofNat 64 b.toNat
    let y := x-(sign <<< 8)
    let mask := (0:BitVec 64)-sign
    (((y ^^^ mask)-mask)+1) >>> 1 = BitVec.ofNat 64 (((if b then 256-L.toNat else L.toNat)+1)/2) := by
  decide +kernel

theorem hiSign_fact : ∀ H : BitVec 8,(H.toNat=0 ∨ H.toNat=255) →
    H.setWidth 64 >>> 7=BitVec.ofNat 64 (decide (H.toNat=255)).toNat := by decide +kernel

theorem wbyte_hi_sign (u j : Nat) :
    (FastNaf.wbyte u (2*j+1)).setWidth 64 >>> 7=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat := by
  rw [hiSign_fact _ (by rw [wbyte_hi_toNat]; split <;> simp),wbyte_hi_toNat]
  cases FastNaf.negative 9 u j <;> rfl

/-- The sign byte of digit `j` (width nine), from `x16` at its digits. -/
theorem fixedSignByte_ok {s : State} {base : Addr} {size bits u j : Nat}
    (hs : Scr s base size) (hb : bits+1<4096) (hj : bits+2*j+1<size)
    (h16 : s.gpr .x16=off base (2*j)) (hm : s.mem (off base (bits+(2*j+1)))=FastNaf.wbyte u (2*j+1)) :
    WP isa (.block [.ldrb .x3 .x16 (bits+1),.lsr .x .x3 .x3 7]) s fun t =>
      t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat ∧ Keeps [.x3] s t := by
  have hrr : InRegions (s.rd++s.wr) (off base (bits+(2*j+1))) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have he : off base (2*j)+BitVec.ofNat 64 (bits+1)=off base (bits+(2*j+1)) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 2*j+(bits+1)=bits+(2*j+1) by omega]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
    RegUpd.gpr_write,BitVec.setWidth_eq,h16,Size.bits,Nat.mod_one,hb,and_self,he,hrr,
    show 7<64 by decide,ite_true,read1_zext,hm,Option.map_some,Option.bind_some,Option.some.injEq,
    exists_eq_left']
  refine ⟨wbyte_hi_sign u j,?_,rfl,rfl,rfl,rfl⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_write,hq,ite_false]

/-- `x2 = (a + 1) / 2` for a magnitude `a` with low byte `L` in `x2` and sign `b` in `x3`. -/
theorem fixedIndexTail_ok {s : State} {L : BitVec 8} {b : Bool}
    (h2 : s.gpr .x2=L.setWidth 64) (h3 : s.gpr .x3=BitVec.ofNat 64 b.toNat) :
    WP isa (.block (Naf.digitIndex.drop 1)) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (((if b then 256-L.toNat else L.toNat)+1)/2) ∧
      Keeps [.x2,.x3,.x4] s t := by
  apply WP.of_runBlock
  simp only [Naf.digitIndex,List.drop_succ_cons,List.drop_zero,runBlock_cons,runStep_some,
    runBlock_nil,exec,read_x,RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,h2,h3,
    show 8<64 by decide,show 1<64 by decide,show 16*0<64 by decide,show 1<4096 by decide,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · exact fixedIndexW_fact L b
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

/-- The generator's digit `j`'s table index `(a + 1) / 2`, for its magnitude `a`. -/
theorem jointFixedIndex_ok {c : Joint.Cfg} {s : State} {u j : Nat} (hg : c.gw=7 ∨ c.gw=9)
    (h2 : s.gpr .x2=jointGCell c u j) (h3 : c.gw=9 → s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64) :
    WP isa (.block (Joint.fixedIndex c)) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 ((FastNaf.magnitude c.gw u j+1)/2) ∧ Keeps [.x2,.x3,.x4] s t := by
  by_cases h9 : c.gw=9
  · rw [jointGCell,ite_eq_left h9] at h2
    rw [Joint.fixedIndex,ite_eq_left h9,
      show (Instr.lsr .x .x3 .x3 7 :: Naf.digitIndex.drop 1)=[.lsr .x .x3 .x3 7]++Naf.digitIndex.drop 1
        from rfl,WP.block_append_iff]
    refine WP.mono (lsr_ok s (d:=.x3) (n:=.x3) (sh:=7) (by decide)) fun a ⟨a3,ka⟩ => ?_
    have a3' : a.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat := by
      rw [a3,h3 h9,wbyte_hi_sign]
    refine WP.mono (fixedIndexTail_ok (L:=FastNaf.wbyte u (2*j)) ((ka.gpr .x2 (by decide)).trans h2) a3')
      fun t ⟨t2,kt⟩ => ⟨?_,(ka.mono (by simp)).trans kt⟩
    rw [t2,h9,wbyte_lo_toNat]
    have hb := fastMagnitude_bound 9 u j
    cases hn : FastNaf.negative 9 u j
    · simp only [Bool.false_eq_true,ite_false]
    · have hp := FastNaf.negative_magnitude_pos 9 u j hn
      simp only [ite_true]
      congr 2; omega
  · have h7 := hg.resolve_right h9
    rw [jointGCell,ite_eq_right h9] at h2
    rw [Joint.fixedIndex,ite_eq_right h9]
    have hbm : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
    refine WP.mono (nafIndex_ok h2) fun t ⟨t2,kt⟩ => ⟨?_,kt⟩
    rw [t2,hbm,h7]

/-- The generator's digit `j`'s sign. -/
theorem jointSignRead_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hg : c.gw=7 ∨ c.gw=9) (hB : c.gBits+1<4096)
    (hj : j<257) (hl : c.gBits+jointGLen c≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hm : ∀ i<jointGLen c,s.mem (off base (c.gBits+i))=jointGByte c u i) :
    WP isa (.block (Joint.signRead c)) s fun t =>
      t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative c.gw u j).toNat ∧ Keeps [.x3,.x16] s t := by
  by_cases h9 : c.gw=9
  · have hlen : jointGLen c=514 := by rw [jointGLen,ite_eq_left h9]
    have g := hm (2*j+1) (by omega)
    rw [jointGByte,ite_eq_left h9] at g
    rw [Joint.signRead,ite_eq_left h9,
      show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x3 .x16 (c.gBits+1),
        .lsr .x .x3 .x3 7] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19]++
        [.ldrb .x3 .x16 (c.gBits+1),.lsr .x .x3 .x3 7] from rfl,WP.block_append_iff]
    refine WP.mono (nafAdd2_ok hs h19) fun a ⟨a16,ka⟩ => ?_
    refine WP.mono (fixedSignByte_ok (u:=u) (hs.of_keeps ka (by decide)) hB (by omega) a16
      (by rw [ka.mem]; exact g)) fun t ⟨t3,kt⟩ => ⟨?_,(ka.mono (by simp)).trans (kt.mono (by simp))⟩
    rw [t3,h9]
  · have h7 := hg.resolve_right h9
    have hlen : jointGLen c=257 := by rw [jointGLen,ite_eq_right h9]
    have g := hm j (by omega)
    rw [jointGByte,ite_eq_right h9] at g
    rw [Joint.signRead,ite_eq_right h9]
    refine WP.mono (nafSignRead_ok (K:=c.G) hs (by change c.gBits<4096; omega)
      (by change c.gBits+j<size; omega) h19 g) fun t ⟨t3,kt⟩ => ⟨?_,kt⟩
    have hbn : nafNegative (FastNaf.byte 7 u j)=FastNaf.negative 7 u j := FastNaf.byte_negative 7 u j
    rw [t3,hbn,h7]

end VG.Proof.Weierstrass.AArch64
