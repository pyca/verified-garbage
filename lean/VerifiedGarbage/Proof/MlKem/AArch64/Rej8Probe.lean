module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `MlKem.AArch64.Rej8Parse`, which this module and modules that import it used -/

section

/-! # Packed twelve-bit candidate decoding for ML-KEM's vector sampler -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- The two bytes of each of eight twelve-bit candidates: bytes `3k, 3k+1`
for candidate `2k` and `3k+1, 3k+2` for candidate `2k+1`. This is the exact
table installed by the parser. -/
def gatherIndex : BitVec 128 := 0x0b0a0a09080707060504040302010100

/-- The byte of the packed stream that byte `e` of the gathered vector holds. -/
def gatherSrc (e : Nat) : Nat := 3*(e/4) + (e%4+1)/2

theorem gatherIndex_byte {e : Nat} (he : e<16) : (vbyte gatherIndex e).toNat = gatherSrc e := by
  have h : ∀ e<16, (vbyte gatherIndex e).toNat = gatherSrc e := by decide +kernel
  exact h e he

def gatherValue (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun e =>
    let i := (vbyte gatherIndex e).toNat
    if i<16 then vbyte x i else 0

/-- The vector table lookup reads the two bytes of each candidate. -/
theorem gather_byte (m : Mem) (p : Addr) {e : Nat} (he : e<16) :
    vbyte (gatherValue (m.read p 16)) e = m (p+BitVec.ofNat 64 (gatherSrc e)) := by
  rw [gatherValue,vbyte_ofVBytes _ he,gatherIndex_byte he]
  have hs : gatherSrc e < 16 := by simp only [gatherSrc]; omega_using [he]
  rw [ite_eq_left hs]
  exact Mem.extractLsb'_read m p hs

/-- Low twelve bits of each packed word: of each even halfword. -/
def lowMask : BitVec 128 := 0x00000fff00000fff00000fff00000fff

/-- Each halfword shifted right by four. -/
def shift4 (x : BitVec 128) : BitVec 128 := ofVHalves fun e => vhalf x e >>> 4

def parsed (x : BitVec 128) : BitVec 128 :=
  let g := gatherValue x
  VSelOp.eval .bif g (shift4 g) lowMask

theorem vhalf_and (x y : BitVec 128) (e : Nat) :
    vhalf (x &&& y) e = vhalf x e &&& vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_and]

theorem bif_half_even (a : BitVec 16) : a ^^^ ((a ^^^ a >>> 4) &&& ~~~4095) = a &&& 4095 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have k : (4095 : BitVec 16).getLsbD i = decide (i<12) := by
    have finite : ∀ j<16, (4095 : BitVec 16).getLsbD j = decide (j<12) := by decide +kernel
    exact finite i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, k, hi,
    decide_true, Bool.true_and]
  by_cases h : i<12
  · simp [h]
  · have : a.getLsbD (4+i) = false := BitVec.getLsbD_of_ge a _ (by omega_using [h])
    simp [h, this]

theorem bif_half_odd (a : BitVec 16) : a ^^^ ((a ^^^ a >>> 4) &&& ~~~(0 : BitVec 16)) = a >>> 4 := by
  rw [show ~~~(0 : BitVec 16) = BitVec.allOnes 16 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
    BitVec.xor_self, BitVec.zero_xor]

theorem vhalf_xor (x y : BitVec 128) (e : Nat) :
    vhalf (x ^^^ y) e = vhalf x e ^^^ vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_xor]

theorem vhalf_not (x : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (~~~x) e = ~~~vhalf x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vhalf, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    show 16*e+i<128 by omega_using [he, hi]]

theorem parsed_lane (x : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (parsed x) e =
      if e % 2 = 0 then vhalf (gatherValue x) e &&& 4095 else vhalf (gatherValue x) e >>> 4 := by
  have hm : vhalf lowMask e = if e % 2 = 0 then 4095 else 0 := by
    have finite : ∀ j < 8, vhalf lowMask j = if j % 2 = 0 then 4095 else 0 := by decide +kernel
    exact finite e he
  simp only [parsed, VSelOp.eval]
  rw [vhalf_xor, vhalf_and, vhalf_xor, vhalf_not _ he, hm, shift4, vhalf_ofVHalves _ he]
  split
  · exact bif_half_even _
  · exact bif_half_odd _

/-- Eight consecutive twelve-bit values, before rejection. -/
def candidate (m : Mem) (p : Addr) (e : Nat) : BitVec 16 :=
  ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).setWidth 16

theorem candidate_lt (m : Mem) (p : Addr) (e : Nat) : (candidate m p e).toNat < 4096 := by
  simp only [candidate, BitVec.toNat_setWidth]
  have := ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).isLt
  omega_using []

theorem parsed_candidate (m : Mem) (p : Addr) {e : Nat} (he : e < 8) :
    vhalf (parsed (m.read p 16)) e = candidate m p e := by
  rw [parsed_lane _ he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hg : ∀ j < 16, (vhalf (gatherValue (m.read p 16)) e).getLsbD j =
      (m (p + BitVec.ofNat 64 (gatherSrc (2*e + j/8)))).getLsbD (j%8) := fun j hj => by
    rw [getLsbD_vhalf _ _ hj, ← gather_byte m p (e := 2*e + j/8) (by omega_using [he, hj])]
    simp only [vbyte, BitVec.getLsbD_extractLsb', show j%8 < 8 by omega_using [], decide_true, Bool.true_and]
    congr 1; omega_using []
  have hc : (candidate m p e).getLsbD i = (decide (i < 12) &&
      (m (p + BitVec.ofNat 64 (3*(e/2) + (12*(e%2)+i)/8))).getLsbD ((12*(e%2)+i)%8)) := by
    simp only [candidate, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    by_cases h : i < 12
    · simp only [h, decide_true, Bool.true_and]
      rw [getLsbD_read m 3 _ _ (by omega_using [h]), Offset.add_add]
    · simp [h]
  rw [hc]
  by_cases hp : e%2=0
  · rw [ite_eq_left hp, BitVec.getLsbD_and, hg i hi]
    have k : (4095 : BitVec 16).getLsbD i = decide (i<12) := by
      have finite : ∀ j<16, (4095 : BitVec 16).getLsbD j = decide (j<12) := by decide +kernel
      exact finite i hi
    rw [k, Bool.and_comm, hp]
    have : gatherSrc (2*e + i/8) = 3*(e/2) + (12*0+i)/8 := by simp only [gatherSrc]; omega_using [hi, hp]
    by_cases h : i < 12
    · rw [this, show (12*0+i)%8 = i%8 by omega_using []]
    · simp [h]
  · rw [ite_eq_right hp, BitVec.getLsbD_ushiftRight]
    have ho : e%2=1 := by omega_using [hp]
    rw [ho]
    by_cases h : i < 12
    · rw [hg (4+i) (by omega_using [h])]
      have : gatherSrc (2*e + (4+i)/8) = 3*(e/2) + (12*1+i)/8 := by simp only [gatherSrc]; omega_using [hi, hp]
      rw [this, show (4+i)%8 = (12*1+i)%8 by omega_using []]
      simp [h]
    · rw [BitVec.getLsbD_of_ge _ (4+i) (by omega_using [h])]
      simp [h]

/-- One symbolic execution for the four-instruction parsing shape. -/
theorem parse_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x2) 16)
    (hi : s.v .v16 = gatherIndex) (hm : s.v .v17 = lowMask) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.parse) s fun t =>
      VChg [.v0,.v1] s t ∧ t.v .v0 = parsed (s.mem.read (s.gpr .x2) 16) := by
  refine wp_ldrq (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha =>
    wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun c hc =>
    wp_vop (d := .v0) rfl fun t ht => wp_nil ?_
  refine ⟨(((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg).mono (by decide), ?_⟩
  rw [ht.v, hc.get .v0, hc.v, hc.get .v17, hb.get .v17, ha.get .v17, hm, hb.v,
    ha.get .v16, hi, ha.v]
  rfl

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! ### `MlKem.AArch64.Rej8Index`, which only this module used -/

section

/-! # Extracting the public rejection mask and table address -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- The low halfword determines the mask and count; the second halfword
included by UMOV does not interfere with either extraction. -/
theorem word_mod {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    (vword x 0).toNat % 65536 = packedCount mask := by
  have h := congrArg BitVec.toNat hx
  rw [← vword_lo x 0, ← BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h
  have hb := packedCount_bound hm
  simpa only [Nat.reducePow, Nat.mod_eq_of_lt (show packedCount mask < 65536 by omega_using [hb])] using h

theorem word_mask {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    ((vword x 0).setWidth 64 &&& 255).toNat = mask := by
  rw [toNat_and_mask _ _ (k := 8) rfl, BitVec.toNat_setWidth]
  have hw := (vword x 0).isLt
  have hl := word_mod hm hx
  have hp := packedCount_mask hm
  omega_using [hl, hp]

theorem word_count {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    (((vword x 0).setWidth 64 >>> 8) &&& 15).toNat =
      (Impl.MlKem.AArch64.Rej8.acceptedLanes mask).length := by
  rw [toNat_and_mask _ _ (k := 4) rfl, toNat_lsr, BitVec.toNat_setWidth]
  have hw := (vword x 0).isLt
  have hl := word_mod hm hx
  have hp := packedCount_count hm
  have hn := accepted_length mask
  omega_using [hl, hp, hn]

def indexCode : List Instr :=
 [.umov .w .x6 .v1 0,.movz .x .x7 255 0,.logic .and .x .x7 .x6 .x7,
 .lsl .x .x7 .x7 4,.add .x .x7 .x16 .x7]

/-- The public table address is exactly sixteen times the accepted mask. -/
theorem index_basic (s : State) {mask : Nat} (hm : mask < 256)
    (hx : vhalf (s.v .v1) 0 = BitVec.ofNat 16 (packedCount mask)) :
    WP isa (.block indexCode) s fun t =>
      Only [.x6,.x7] s t ∧
      t.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 ∧
      t.gpr .x7 = s.gpr .x16 + BitVec.ofNat 64 (16*mask) := by
  let a := s.write .w .x6 (vword (s.v .v1) 0)
  have ha : Only [.x6] s a := only_write _ _ _ _
  have h6 : a.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 := by
    rfl
  refine WP.cons (s' := a) rfl ?_
  refine wp_movz fun b hb eb => wp_and fun c hc ec => wp_lsl (by decide) fun d hd ed =>
    wp_add fun t ht et => wp_nil ?_
  have h7 : (c.gpr .x7).toNat=mask := by
    rw [ec,hb.get .x6,h6,eb]
    exact word_mask hm hx
  have hs : d.gpr .x7=BitVec.ofNat 64 (16*mask) := by
    apply BitVec.eq_of_toNat_eq
    rw [ed,toNat_lsl_n (by rw [h7]; omega_using [hm]),h7,BitVec.toNat_ofNat]
    omega_using [hm]
  refine ⟨((((ha.trans hb).trans hc).trans hd).trans ht).mono (by decide), ?_, ?_⟩
  · rw [ht.get .x6,hd.get .x6,hc.get .x6,hb.get .x6,h6]
  · rw [et,hs,hd.get .x16,hc.get .x16,hb.get .x16,ha.get .x16]

theorem index_ok (s : State) {mask : Nat} (hm : mask < 256)
    (hx : vhalf (s.v .v1) 0 = BitVec.ofNat 16 (packedCount mask)) :
    WP isa (.block indexCode) s fun t =>
      Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 ∧
      t.gpr .x7 = s.gpr .x16 + BitVec.ofNat 64 (16*mask) := by
  exact WP.mono (WP.keepV (by rfl : indexCode.all (fun i => !writesV i)=true)
    (index_basic s hm hx)) fun _ ⟨⟨hk,h6,h7⟩,hv⟩ => ⟨hk,hv,h6,h7⟩

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! ### `MlKem.AArch64.Rej8Mask`, which only this module used -/

section

/-! # Connecting acceptance predicates to the packed table index and count -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Sum.lean`, which only this module imported.
section

/-! # Exact SIMD horizontal sum used for the rejection mask -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

def sum8 (x : BitVec 128) : BitVec 16 :=
  vhalf x 0 + vhalf x 1 + vhalf x 2 + vhalf x 3 +
  vhalf x 4 + vhalf x 5 + vhalf x 6 + vhalf x 7

theorem laneSum_h8 (x : BitVec 128) :
    VArr.h8.laneSum x = (vhalf x 0).toNat + (vhalf x 1).toNat + (vhalf x 2).toNat + (vhalf x 3).toNat +
      (vhalf x 4).toNat + (vhalf x 5).toNat + (vhalf x 6).toNat + (vhalf x 7).toNat := by
  have h : ∀ i, (BitVec.setWidth 128 (vhalf x i)).toNat = (vhalf x i).toNat := fun i => by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (vhalf x i).isLt (by decide))]
  rw [VArr.laneSum, VArr.lanes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h]
  omega_using []

theorem sum8_toNat (x : BitVec 128) : (sum8 x).toNat = ((vhalf x 0).toNat + (vhalf x 1).toNat + (vhalf x 2).toNat +
    (vhalf x 3).toNat + (vhalf x 4).toNat + (vhalf x 5).toNat + (vhalf x 6).toNat + (vhalf x 7).toNat) % 2 ^ 16 := by
  simp only [sum8, BitVec.toNat_add, Nat.mod_add_mod]

theorem addv_half (x : BitVec 128) :
    vhalf (BitVec.ofNat 128 (VArr.h8.laneSum x % 2 ^ 16)) 0 = sum8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [sum8_toNat, ← laneSum_h8, vhalf, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (show VArr.h8.laneSum x % 2 ^ 16 < 2 ^ 128 from Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
    Nat.mod_mod]

/-- The horizontal sum before UMOV: `addv h1, v1.8h`. -/
def sumCode : List Instr := [.vop (.addv .h8 .v1 .v1)]

theorem sumCode_ok (s : State) :
    WP isa (.block sumCode) s fun t => VChg [.v1] s t ∧ vhalf (t.v .v1) 0 = sum8 (s.v .v1) := by
  refine wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨ht.chg, ?_⟩
  rw [ht.v]
  exact addv_half _

end VG.Proof.MlKem.AArch64.Rej8
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8

def mask8 (a b c d e f g h : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
  (if d then 8 else 0) + (if e then 16 else 0) + (if f then 32 else 0) +
  (if g then 64 else 0) + (if h then 128 else 0)

def weight8 (a b c d e f g h : Bool) : BitVec 16 :=
  (if a then BitVec.ofNat 16 257 else 0) + (if b then BitVec.ofNat 16 258 else 0) + (if c then BitVec.ofNat 16 260 else 0) +
  (if d then BitVec.ofNat 16 264 else 0) + (if e then BitVec.ofNat 16 272 else 0) + (if f then BitVec.ofNat 16 288 else 0) +
  (if g then BitVec.ofNat 16 320 else 0) + (if h then BitVec.ofNat 16 384 else 0)

theorem mask8_bound : ∀ a b c d e f g h, mask8 a b c d e f g h < 256 := by decide +kernel

theorem mask8_bits : ∀ a b c d e f g h, ∀ i < 8,
    ((mask8 a b c d e f g h / 2^i)%2 == 1) = [a,b,c,d,e,f,g,h].getD i false := by decide +kernel

theorem weight8_exact : ∀ a b c d e f g h,
    weight8 a b c d e f g h = BitVec.ofNat 16 (packedCount (mask8 a b c d e f g h)) := by decide +kernel

/-- Acceptance mask of eight decoded candidates. -/
def acceptanceMask (x : BitVec 128) : Nat :=
  mask8 (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
    (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
    (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
    (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

theorem acceptanceMask_bound (x : BitVec 128) : acceptanceMask x < 256 := mask8_bound ..

theorem acceptanceMask_bits (x : BitVec 128) {i : Nat} (hi : i < 8) :
    ((acceptanceMask x / 2^i)%2 == 1) = decide ((vhalf x i).toNat < 3329) := by
  rw [acceptanceMask,mask8_bits _ _ _ _ _ _ _ _ i hi]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- The horizontal sum really is the table index and accepted count for
these candidates, without modular overflow in the halfword lanes. -/
theorem accepted_sum {x y : BitVec 128}
    (hy : ∀ i < 8, vhalf y i = if (vhalf x i).toNat < 3329 then BitVec.ofNat 16 (256+2^i) else 0) :
    sum8 y = BitVec.ofNat 16 (packedCount (acceptanceMask x)) := by
  rw [sum8,hy 0 (by decide),hy 1 (by decide),hy 2 (by decide),hy 3 (by decide),
    hy 4 (by decide),hy 5 (by decide),hy 6 (by decide),hy 7 (by decide)]
  simpa only [weight8, decide_eq_true_eq, Nat.reducePow, Nat.reduceAdd, acceptanceMask] using
    weight8_exact (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
      (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
      (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
      (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Composition of vector parsing, acceptance, horizontal sum and lookup index -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Accept.lean`, which only this module imported.
section

/-! # Machine-code acceptance bits for eight ML-KEM candidates -/

section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- One lane of `cmhi` (`3329 > x`) and the weight: the weight exactly when `x < 3329`. -/
theorem cmp_lane (x w : BitVec 16) :
    (if VCmpOp.hi.test (3329 : BitVec 16) x = true then BitVec.allOnes 16 else 0) &&& w =
      if x.toNat < 3329 then w else 0 := by
  by_cases h : x.toNat < 3329
  · simp only [VCmpOp.test, show (3329 : BitVec 16).toNat = 3329 from rfl, gt_iff_lt, h, decide_true,
      ite_true]
    exact BitVec.allOnes_and
  · simp [VCmpOp.test, h]

/-- The SIMD acceptance block preserves memory, scalar registers and every
other vector register; each of its lanes contains exactly its accepted
mask/count weight, or zero. -/
theorem accept_ok (s : State)
    (hq : ∀ e < 8, vhalf (s.v .v19) e = 3329)
    (hw : ∀ e < 8, vhalf (s.v .v20) e = BitVec.ofNat 16 (256 + 2^e))
    (_hz : ∀ e < 8, (vhalf (s.v .v0) e).toNat < 4096) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.accept) s fun t =>
      VChg [.v1] s t ∧ ∀ e < 8, vhalf (t.v .v1) e =
        if (vhalf (s.v .v0) e).toNat < 3329 then BitVec.ofNat 16 (256+2^e) else 0 := by
  refine wp_vop (d := .v1) rfl fun a ha =>
    wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨(ha.chg.trans ht.chg).mono (by decide), ?_⟩
  intro e he
  rw [ht.v, vhalf_and, ha.v, vhalf_map2 _ _ _ he, ha.get .v20, hw e he, hq e he]
  exact cmp_lane _ _

end VG.Proof.MlKem.AArch64.Rej8
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def probeCode : List Instr := Impl.MlKem.AArch64.Rej8.parse ++
  Impl.MlKem.AArch64.Rej8.accept ++ sumCode ++ indexCode

structure Constants (s : State) : Prop where
  index : s.v .v16=gatherIndex
  mask : s.v .v17=lowMask
  q : ∀ i<8,vhalf (s.v .v19) i=3329
  weights : ∀ i<8,vhalf (s.v .v20) i=BitVec.ofNat 16 (256+2^i)
  zero : ∀ i<8,vhalf (s.v .v21) i=0

def candidatesAt (s : State) : BitVec 128 := parsed (s.mem.read (s.gpr .x2) 16)
def maskAt (s : State) : Nat := acceptanceMask (candidatesAt s)

structure ProbePost (s t : State) : Prop where
  keep : Keep [.x6,.x7] s t
  mem : t.mem=s.mem
  other : ∀ r, r ∉ [.v0,.v1,.v2] → t.v r=s.v r
  values : t.v .v0=candidatesAt s
  index : t.gpr .x7=s.gpr .x16+BitVec.ofNat 64 (16*maskAt s)
  count : ((t.gpr .x6 >>> 8) &&& 15).toNat=(Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length

theorem probe_ok (s : State) (hc : Constants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16) :
    WP isa (.block probeCode) s (fun t => ProbePost s t) := by
  rw [probeCode,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (parse_ok s hr hc.index hc.mask) fun a ⟨ha,hav⟩ => ?_
  refine WP.mono (accept_ok a (fun i hi => by rw [ha.get .v19]; exact hc.q i hi)
    (fun i hi => by rw [ha.get .v20]; exact hc.weights i hi)
    (fun i hi => by rw [hav,parsed_candidate _ _ hi]; exact candidate_lt _ _ _)) fun b ⟨hb,hbv⟩ => ?_
  refine WP.mono (sumCode_ok b) fun c ⟨hc0,hcv⟩ => ?_
  have hmask : vhalf (c.v .v1) 0 = BitVec.ofNat 16 (packedCount (maskAt s)) := by
    rw [hcv,accepted_sum hbv,hav]
    rfl
  refine WP.mono (index_ok c (acceptanceMask_bound _) hmask) fun t ⟨ht,htv,h6,h7⟩ => ?_
  have hall := ((ha.trans hb).trans hc0).mono (rs' := [.v0,.v1,.v2]) (by decide)
  refine ⟨(hall.keep.trans ht.keep).mono (by decide),ht.mem.trans hall.mem,?_,?_,?_,?_⟩
  · intro r hr0
    rw [htv,hall.get r hr0]
  · rw [htv,hc0.get .v0,hb.get .v0,hav]
    rfl
  · rw [h7,hall.gpr]
    rfl
  · rw [h6]
    exact word_count (acceptanceMask_bound _) hmask

end VG.Proof.MlKem.AArch64.Rej8
