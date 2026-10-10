import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackStreamMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackAdvance

/-! ## From `KeygenPackTailMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

theorem slice_word (G base sh w : Nat) (h : sh+w≤64) :
    ((BitVec.ofNat 64 (G/2^base))>>>sh).setWidth w=BitVec.ofNat w (G/2^(base+sh)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow,VG.Proof.MlKem.mod_pow_div_mod _ h,
    Nat.div_div_eq_div_mul,←Nat.pow_add,BitVec.toNat_ofNat]

theorem narrow_word (G base w : Nat) (h : w≤64) :
    (BitVec.ofNat 64 (G/2^base)).setWidth w=BitVec.ofNat w (G/2^base) := by
  simpa only [BitVec.ushiftRight_zero,Nat.add_zero] using slice_word G base 0 w (by omega)

theorem smallWord_byte (G k n : Nat) {j : Nat} (hj : j<n) :
    (BitVec.ofNat (8*n) (G/2^(8*k))).extractLsb' (8*j) 8=byteOf G (k+j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    VG.Proof.MlKem.mod_pow_div_mod _ (by omega),Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]
  rfl

theorem written_small (G k n : Nat) (m : Mem) (out : Addr) :
    Written m (m.writeW out (BitVec.ofNat (8*n) (G/2^(8*k)))) out n (fun j=>byteOf G (k+j)) :=
  (written_word m out n _).congr fun _j hj=>smallWord_byte G k n hj


theorem narrow_zero (G w : Nat) (h : w≤64) :
    (BitVec.ofNat 64 G).setWidth w=BitVec.ofNat w G := by
  simpa only [Nat.pow_zero,Nat.div_one] using narrow_word G 0 w h

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
  have hdiv : d*c/8/8=d*c/64 := by omega
  have hacc : acc64 G d c=G/2^(8*(d*c/8/8*8)) := by
    rw [acc64,Nat.mod_eq_of_lt hG,hdiv]
    congr 2
    omega
  rw [ha hnz,hacc]
  have htail := tail_written (d*c/8) (G/2^(8*(d*c/8/8*8))) ht
    (fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ c).mem out
  have htail' := htail.congr fun j _=>byteOf_div G (d*c/8/8*8) j
  have hbase : d*c/8/8*8=8*(d*c/64) := by omega
  rw [hbase] at htail'
  have hlength : 8*(d*c/64)+d*c/8%8=d*c/8 := by omega
  have hh := written_append hw htail' (by have := Nat.mul_le_mul hd hc; omega)
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
