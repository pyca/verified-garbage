module

public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackDigits
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.Mem
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `MlDsa.AArch64.Optimized.HighPackMemory`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

def storePacked (width : Nat) (m : Mem) (a : Addr) (x : BitVec 128) : Mem :=
  let lo := m.writeW a (x.extractLsb' 0 64)
  if width=4 then lo else lo.writeW (a+8) (x.extractLsb' 64 32)

/-- Both packing formats write only the exact eight- or twelve-byte block. -/
theorem storePacked_frame (m : Mem) (a : Addr) (x : BitVec 128) {width : Nat}
    (hw : width=4 ∨ width=6) : Frame [⟨a,2*width⟩] m (storePacked width m a x) := by
  have h8 : 8≤2*width := by omega_using [hw]
  have h0 : (Region.mk a (2*width)).Contains a 8 := by
    simpa only [BitVec.add_zero] using
      (Offset.contains_base a (d := 0) h8 (by decide))
  have h := (Frame.refl [⟨a,2*width⟩] m).writeW (List.mem_singleton_self _) (x.extractLsb' 0 64) h0
  rcases hw with rfl | rfl
  · exact h
  · exact h.writeW (List.mem_singleton_self _) (x.extractLsb' 64 32)
      (Offset.contains_base a (d := 8) (by decide) (by decide))

private theorem storeSlice_byte (m : Mem) (a : Addr) (x : BitVec 128)
    {start count i : Nat} (hi : i<count) (hc : count<2^64) :
    m.writeW a (x.extractLsb' start (8*count)) (a+BitVec.ofNat 64 i)=
      x.extractLsb' (start+8*i) 8 := by
  simp only [Mem.writeW,show 8*count/8=count by omega_using [],Mem.write,
    Mem.sub_ofNat_toNat a (Nat.lt_trans hi hc),hi,ite_true]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
  have hb' : 8*i+b<8*count := by omega_using [hi, hb]
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',
    show 8*i+b<8*(8*count/8) by omega_using [hi, hb],hb',decide_true,Bool.true_and]
  congr 1
  omega_using []

/-- The stored bytes are exactly the low bytes of the vector, including
unaligned output addresses and modular address arithmetic. -/
theorem storePacked_byte (m : Mem) (a : Addr) (x : BitVec 128) {width i : Nat}
    (hw : width=4 ∨ width=6) (hi : i<2*width) :
    storePacked width m a x (a+BitVec.ofNat 64 i)=vbyte x i := by
  rcases hw with rfl | rfl
  · simpa only [storePacked,ite_true,vbyte,Nat.zero_add] using
      storeSlice_byte m a x (start := 0) (count := 8) hi (by decide)
  · by_cases h8 : i<8
    · unfold storePacked
      simp only [show ¬(6:Nat)=4 by decide,ite_false]
      have ho : ¬((a+BitVec.ofNat 64 i)-(a+8)).toNat<4 := by bv_omega
      change Mem.write _ (a+8) 4 _ _ = _
      rw [Mem.write_apply ho]
      simpa only [vbyte,Nat.zero_add] using
        storeSlice_byte m a x (start := 0) (count := 8) h8 (by decide)
    · have ha : a+BitVec.ofNat 64 i=(a+8)+BitVec.ofNat 64 (i-8) := by bv_omega
      unfold storePacked
      simp only [show ¬(6:Nat)=4 by decide,ite_false]
      rw [ha,storeSlice_byte _ _ x (start := 64) (count := 4) (by omega_using [hi]) (by decide)]
      change x.extractLsb' (64+8*(i-8)) 8=x.extractLsb' (8*i) 8
      congr 1
      omega_using [h8]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

end

/-! ### `MlDsa.AArch64.Optimized.HighPackBlock`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

structure PackConstants (s : State) : Prop where
  zero : s.v .v28=0
  idx29 : s.v .v29=ofVDwords 0x0908060504020100 0xffffffff0e0d0c0a
  idx24 : s.v .v24=ofVDwords 0xffff0504ffff0100 0xffff0d0cffff0908
  idx25 : s.v .v25=ofVDwords 0xffff0706ffff0302 0xffff0f0effff0b0a

structure PackReady (g : Nat) (s : State) : Prop extends HighConstants g s, PackConstants s

def packedVector (width : Nat) (s : State) : BitVec 128 :=
  if width=4 then packed4 s else packed6 s

structure TailPost (g : Nat) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀ r, r∉[.v4,.v5,.v6] → t.v r=s.v r
  ready : PackReady g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    vbyte (packedVector (packWidth g) s) i

/-- The tail's exact register and memory effects, shared by both parameter choices. -/
theorem tailPost_of_store {g : Nat} (hg : IsG g) {s t : State} (hc : PackReady g s)
    (hk : Keep [.x9] s t) (hv : ∀ r, r∉[.v4,.v5,.v6] → t.v r=s.v r)
    (hm : t.mem=storePacked (packWidth g) s.mem (s.gpr .x1) (packedVector (packWidth g) s)) :
    TailPost g s t := by
  have hw : packWidth g=4 ∨ packWidth g=6 := by rcases hg with rfl | rfl <;> decide
  refine ⟨hk,hv,?_,?_,?_⟩
  · refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [hv .v17 (by decide)]; exact hc.add
    · rw [hv .v18 (by decide)]; exact hc.mul
    · rw [hv .v19 (by decide)]; exact hc.round
    · rw [hv .v20 (by decide)]; exact hc.modulus
    · rw [hv .v28 (by decide)]; exact hc.zero
    · rw [hv .v29 (by decide)]; exact hc.idx29
    · rw [hv .v24 (by decide)]; exact hc.idx24
    · rw [hv .v25 (by decide)]; exact hc.idx25
  · rw [hm]; exact storePacked_frame _ _ _ hw
  · intro i hi; rw [hm]; exact storePacked_byte _ _ _ hw hi

theorem packTail_ok {g : Nat} (hg : IsG g) {s : State} (hc : PackReady g s)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, TailPost g s t → WP isa (.block rest) t Q) :
    WP isa (.block (packTail (packWidth g) ++ rest)) s Q := by
  have hw : packWidth g=4 ∨ packWidth g=6 := by rcases hg with rfl | rfl <;> decide
  rcases hw with hw | hw
  · rw [hw]
    refine packTail4_ok hw8 fun t ht hv hm => k t (tailPost_of_store hg hc ht hv ?_)
    simpa only [hw,storePacked,packedVector,ite_true] using hm
  · rw [hw]
    refine packTail6_ok hw8 (hw4 hw) fun t ht hv hm => k t (tailPost_of_store hg hc ht hv ?_)
    simpa only [hw,storePacked,packedVector,show ¬(6:Nat)=4 by decide,ite_false] using hm


/-- Initialize the arithmetic and packing tables together, with exact frames. -/
theorem setup_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (constants g ++ packSetup)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] s t ∧
      PackReady g t := by
  rw [WP.block_append_iff]
  refine WP.mono (constants_ready s hg) fun a ha => ?_
  refine WP.mono (packSetup_ok a) fun t ht => ?_
  refine ⟨ha.1.trans ht.1,⟨?_,?_,?_,?_⟩,⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩⟩
  · rw [ht.1.vec .v17 (by decide)]; exact ha.2.add
  · rw [ht.1.vec .v18 (by decide)]; exact ha.2.mul
  · rw [ht.1.vec .v19 (by decide)]; exact ha.2.round
  · rw [ht.1.vec .v20 (by decide)]; exact ha.2.modulus

/-- Arithmetic temporaries never overlap the setup vectors. -/
theorem PackReady.afterLoads {g : Nat} {s t : State} (h : PackReady g s)
    (k : VG.Proof.MlKem.AArch64.VChg [.v0,.v1,.v2,.v3,.v7] s t) : PackReady g t := by
  refine ⟨h.toHighConstants.chg k (by decide) (by decide) (by decide) (by decide),⟨?_,?_,?_,?_⟩⟩
  · rw [k.get .v28]; exact h.zero
  · rw [k.get .v29]; exact h.idx29
  · rw [k.get .v24]; exact h.idx24
  · rw [k.get .v25]; exact h.idx25

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits take_drop_eq)

private theorem getD_bound {L : List Nat} {d i : Nat}
    (h : ∀ a∈L, a<2^d) (hi : i<L.length) : L.getD i 0<2^d := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact h _ (List.getElem_mem hi)

/-- A four-bit packing byte is exactly one adjacent pair in the bit-level encoding. -/
theorem encode4_byte {L : List Nat} (hlen : L.length=256) (hbound : ∀ a∈L,a<16)
    {s : State} {block i : Nat} (hb : block<16) (hi : i<8)
    (hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8 (L.getD (16*block+j) 0)) :
    vbyte (packed4 s) i=(bitsToBytes (fieldBits 4 L))[8*block+i]! := by
  have h0 : L.getD (16*block+2*i) 0<16 := getD_bound (d := 4) (i := 16*block+2*i) hbound (by rw [hlen]; omega_using [hb, hi])
  have h1 : L.getD (16*block+(2*i+1)) 0<16 := getD_bound (d := 4) (i := 16*block+(2*i+1)) hbound (by rw [hlen]; omega_using [hb, hi])
  have n0 : (BitVec.ofNat 8 (L.getD (16*block+2*i) 0)).toNat=L.getD (16*block+2*i) 0 := by
    rw [BitVec.toNat_ofNat]; omega_using [h0]
  have n1 : (BitVec.ofNat 8 (L.getD (16*block+(2*i+1)) 0)).toNat=L.getD (16*block+(2*i+1)) 0 := by
    rw [BitVec.toNat_ofNat]; omega_using [h1]
  rw [packed4_byte s hi,hv (2*i) (by omega_using [hi]),hv (2*i+1) (by omega_using [hi]),
    nibble_digits _ _ (by rw [n0]; exact h0) (by rw [n1]; exact h1),n0,n1]
  have hpack := pack_group (d := 4) (c := 2) (nb := 1) (by decide) (by decide)
    hlen hbound (g := 8*block+i) (t := 0) (by decide) (by omega_using [hb, hi])
  simp only [Nat.one_mul,Nat.add_zero,Nat.mul_zero,Nat.pow_zero,Nat.div_one] at hpack
  rw [hpack,take_drop_eq _ 0 (by rw [hlen]; omega_using [hb, hi])]
  simp only [show List.range 2=[0,1] from rfl,List.map_cons,List.map_nil,Nat.add_zero]
  rw [show 2*(8*block+i)=16*block+2*i by omega_using [],
    show 16*block+2*i+1=16*block+(2*i+1) by omega_using []]


/-- A six-bit packing byte agrees with the corresponding four-field group
in the original bit-level encoding. -/
theorem encode6_byte {L : List Nat} (hlen : L.length=256) (hbound : ∀ a∈L,a<64)
    {s : State} {block i : Nat} (hb : block<16) (hi : i<12)
    (hc : PackConstants s)
    (hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8 (L.getD (16*block+j) 0)) :
    vbyte (packed6 s) i=(bitsToBytes (fieldBits 6 L))[12*block+i]! := by
  have bound (k : Nat) (hk : k<4) : L.getD (16*block+(4*(i/3)+k)) 0<64 :=
    getD_bound (d := 6) (i := 16*block+(4*(i/3)+k)) hbound (by rw [hlen]; omega_using [hb, hi, hk])
  have natv (k : Nat) (hk : k<4) :
      (BitVec.ofNat 8 (L.getD (16*block+(4*(i/3)+k)) 0)).toNat=L.getD (16*block+(4*(i/3)+k)) 0 := by
    rw [BitVec.toNat_ofNat]
    have := bound k hk
    omega_using [this]
  rw [packed6_byte s hc.zero hc.idx24 hc.idx25 hc.idx29 hi,
    hv (4*(i/3)) (by omega_using [hi]),hv (4*(i/3)+1) (by omega_using [hi]),
    hv (4*(i/3)+2) (by omega_using [hi]),hv (4*(i/3)+3) (by omega_using [hi])]
  have b0 := bound 0 (by decide)
  have n0 := natv 0 (by decide)
  simp only [Nat.add_zero] at b0 n0
  rw [sixWord_byte_digits _ _ _ _ (by rw [n0]; exact b0)
    (by rw [natv 1 (by decide)]; exact bound 1 (by decide))
    (by rw [natv 2 (by decide)]; exact bound 2 (by decide))
    (by rw [natv 3 (by decide)]; exact bound 3 (by decide)),
    n0,natv 1 (by decide),natv 2 (by decide),natv 3 (by decide)]
  have hpack := pack_group (d := 6) (c := 4) (nb := 3) (by decide) (by decide)
    hlen hbound (g := 4*block+i/3) (t := i%3) (by omega_using []) (by omega_using [hb, hi])
  rw [show 3*(4*block+i/3)+i%3=12*block+i by omega_using []] at hpack
  rw [hpack,take_drop_eq _ 0 (by rw [hlen]; omega_using [hb, hi])]
  simp only [show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,Nat.add_zero]
  rw [show 4*(4*block+i/3)=16*block+4*(i/3) by omega_using [],
    show 16*block+4*(i/3)+1=16*block+(4*(i/3)+1) by omega_using [],
    show 16*block+4*(i/3)+2=16*block+(4*(i/3)+2) by omega_using [],
    show 16*block+4*(i/3)+3=16*block+(4*(i/3)+3) by omega_using []]


/-- The selected vector tail encodes exactly the original polynomial's
HighBits at every byte of a sixteen-coefficient block. -/
theorem packedVector_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {s : State} {m : Mem} {a : Addr} (hr : Reduced m a) (hc : PackConstants s)
    {block i : Nat} (hb : block<16) (hi : i<2*packWidth g)
    (h : ∀ j<4, ∀ e<4,
      vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=
        highWord g (vword (m.read ((a+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)) :
    vbyte (packedVector (packWidth g) s) i=(highPacked g (polyAt m a))[(2*packWidth g)*block+i]! := by
  have hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8
      ((highCoefficients g (polyAt m a)).toList.getD (16*block+j) 0) := by
    intro j hj
    have hjn : 16*block+j<n := by change 16*block+j<256; omega_using [hb, hj]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hjn),Option.getD_some]
    exact gathered_coefficients hg hr hb h hj
  have hlen : (highCoefficients g (polyAt m a)).toList.length=256 := by simp [n]
  have hbound := highCoefficients_bound hg (polyAt m a)
  rw [highPacked,simpleBitPack_eq,packWidth_eq hg]
  rcases hg with rfl | rfl
  · exact encode4_byte hlen hbound hb hi hv
  · exact encode6_byte hlen (fun x hx => hbound x hx) hb hi hc hv

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
