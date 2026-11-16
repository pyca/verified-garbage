module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextView
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Context
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMask
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
import VerifiedGarbage.Proof.Mont.WordsCanonical

/-! ### `Ffdh.AArch64.Cached.Sample`, which only this module used -/

section

/-! The full native sampler applies the public policy to the complete entropy draw. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleWidth.lean`, which only this module imported.
section

/-! The native mask and byte count encode exactly the reviewed sampler width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Proof.Ffdh

theorem sample_width {N : Nat} (positive : 0<N) : ScalarWidth.width N=(N+7)/8 := by
 unfold ScalarWidth.width
 omega_using [positive]

theorem sample_headBits {N : Nat} (positive : 0<N) : ScalarWidth.headBits N=(N-1)%8+1 := by
 unfold ScalarWidth.headBits
 rw [sample_width positive]
 omega_using [positive]

theorem sample_mask {N : Nat} (positive : 0<N) : (sampleMask N).setWidth 8=ScalarWidth.mask N := by
 unfold sampleMask ScalarWidth.mask
 rw [sample_headBits positive]
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega_using []

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleDraw.lean`, which only this module imported.
section

/-! The existing constant-time byte-copy loop realizes the reviewed modular entropy cut. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh

theorem sampleDraw_bytes {s t : State} {rp xp : Addr} {rb : List Byte} {k ld : Nat} {msk : Addr}
 (inv : VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb ld msk k t)
 (length : rb.length=k) (inside : ld<k) :
 Spec.Rsa.bytesAt t.mem xp k=KeyScalar.cut rb ld (msk.setWidth 8) := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,KeyScalar.cut_length _ (length ▸ inside)]
   exact length.symm
 · intro i hi _
   obtain bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   rw [inv.bytes i bound,KeyScalar.cut_get _ (length ▸ inside) (by omega_using [length, bound] : i<rb.length)]
   unfold VG.Proof.Ffdh.AArch64.GenerateKey.cb
   simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega_using [length, bound] : i<rb.length),Option.getD_some]

theorem sampleDraw_ok {s : State} {rp xp : Addr} {rb : List Byte} {k N : Nat}
 (positive : 0<k) (size : k<2^31) (widthPositive : 0<N) (widthFit : N≤8*k) (length : rb.length=k)
 (random : s.gpr .x1=rp) (output : s.gpr .x2=xp) (index : s.gpr .x10=0#64)
 (skip : s.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8)) (mask : s.gpr .x12=sampleMask N)
 (allOnes : s.gpr .x13=255#64) (zero : s.gpr .x7=0#64) (count : s.gpr .x14=BitVec.ofNat 64 k)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (rp+BitVec.ofNat 64 i) 1)
 (bytes : ∀ i<k,s.mem (rp+BitVec.ofNat 64 i)=rb.getD i 0)
 (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa (countLoop .x14 VG.Impl.Ffdh.AArch64.Domain.GenerateKey.cutBody) s fun t =>
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb (k-(N+7)/8) (sampleMask N) k t := by
 obtain inside : k-(N+7)/8<k := by omega_using [positive, widthPositive]
 refine WP.mono (VG.Proof.Ffdh.AArch64.GenerateKey.cut_ok (by omega_using [positive]) size inside random output
  index skip mask allOnes zero count readable bytes writable separate) ?_
 intro t inv
 refine ⟨?_,inv⟩
 rw [sampleDraw_bytes inv length inside,sample_mask widthPositive]
 obtain width := sample_width widthPositive
 rw [←width]
 obtain cut := ScalarWidth.cut_value (bits:=N) (by omega_using [positive, length] : 0<rb.length) (by omega_using [widthFit, length] : N≤8*rb.length)
 rw [length] at cut
 exact cut

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem sample_ok {s : State} {B xp rp : Addr} {Z w k N : Nat} {mi : BitVec 64} {rb : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<k) (size : k<2^31)
 (bitsPositive : 0<N) (bitsBound : N≤8192) (width : N≤8*k) (rbLength : rb.length=k)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (bytes : word s.mem B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8))
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (x : word s.mem B (8*sX)=xp) (random : word s.mem B (8*sRand)=rp)
 (source : Src s B Z rp rb) (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa Generate.sample s fun t =>
 Good t B Z w mi ∧
 Spec.Rsa.bytesAt t.mem xp k=VG.Proof.Ffdh.KeyScalar.cut rb (k-(N+7)/8) ((sampleMask N).setWidth 8) ∧
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 (∀ q,ofs B q<Z→t.mem q=(s.mem.writeW (off B (8*sMask)) (sampleMask N)) q) ∧
 Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem t.mem ∧ Keep mmRegs s t := by
 obtain room256 : 256≤Z := by dsimp only [slot,hdrBytes] at room;omega_using [room]
 unfold Generate.sample
 rw [WP.seq_iff]
 refine WP.mono (sampleMask_ok good.scr room256 good.x0 bitsPositive bitsBound bits) ?_
 rintro a ⟨maskA,maskHeaderA,memA,frameA,restA⟩
 obtain goodA := good_after_header good (by decide) (by decide) frameA restA ((restA.gpr .x0 (by decide)).trans good.x0)
 obtain inscrA : InScr B Z s.mem a.mem := InScr.of_outside frameA (by have := hdr_lt_slot w 8 (show sMask<32 by decide);omega_using [room, this])
 rw [WP.seq_iff]
 have headerA (i : Nat) (hi : i<32) (different : i≠sMask) : word a.mem B (8*i)=word s.mem B (8*i) :=
  header_other frameA (by decide) hi different
 obtain subtract : BitVec.ofNat 64 k-BitVec.ofNat 64 ((N+7)/8)=BitVec.ofNat 64 (k-(N+7)/8) :=
  BitVec.ofNat_sub_ofNat_of_le k ((N+7)/8) (by omega_using [bitsBound]) (by omega_using [width])
 refine WP.mono (WP.keep [.x1,.x2,.x7,.x10,.x11,.x13,.x14] (Q:=fun b =>
  b.gpr .x1=rp ∧ b.gpr .x2=xp ∧ b.gpr .x10=0#64 ∧ b.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8) ∧
  b.gpr .x13=255#64 ∧ b.gpr .x7=0#64 ∧ b.gpr .x14=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sLen<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sX<32 by decide),hdr_enc (show sRand<32 by decide),
    header_read goodA room (show sLen<32 by decide),header_read goodA room (show sBytes<32 by decide),
    header_read goodA room (show sX<32 by decide),header_read goodA room (show sRand<32 by decide),
    (headerA sLen (by decide) (by decide)).trans length,(headerA sBytes (by decide) (by decide)).trans bytes,
    (headerA sX (by decide) (by decide)).trans x,(headerA sRand (by decide) (by decide)).trans random,subtract]
 · rintro b ⟨⟨ptrB,outB,indexB,skipB,onesB,zeroB,countB,memB⟩,restB⟩
   obtain total := restA.trans restB
   obtain sourceB := (source.congrK inscrA restA).congrK (fun q _ =>by rw [memB]) restB
   refine WP.mono (sampleDraw_ok positive size bitsPositive width rbLength ptrB outB indexB skipB
    ((restB.gpr .x12 (by decide)).trans maskA) onesB zeroB countB
    (fun i hi =>sourceB.rd i (by omega_using [rbLength, hi])) (fun i hi =>(src_source sourceB).bytes i (by omega_using [rbLength, hi]))
    (fun i hi =>by rw [total.wr];exact writable i hi) separate) ?_
   rintro t ⟨valueT,inv⟩
   have sameScratch (q : Addr) (hq : ofs B q<Z) : t.mem q=a.mem q := by
    rw [inv.frame q ?_,memB]
    intro i hi eq
    obtain sep : k≤ofs xp q := le_ofs_of_sep outside hq
    rw [eq,show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at sep
    omega_using [room, positive, size, bitsPositive, bitsBound, width, rbLength, bits, bytes, length, x, random, room256, maskA, maskHeaderA, subtract, ptrB, outB, indexB, skipB, onesB, zeroB, countB, valueT, hq, hi, sep]
   obtain rest : Keep mmRegs s t := (total.trans inv.keep).mono (by simp [mmRegs])
   obtain goodT : Good t B Z w mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,
     (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega_using [room, this])).trans goodA.hdr.hw,
     (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sMinv<32 by decide);omega_using [room, this])).trans goodA.hdr.hminv,
     fun i hi =>(workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sArr i<32 by unfold sArr;omega_using [hi]);omega_using [room, this])).trans (goodA.hdr.harr i hi)⟩
   obtain outsideX : Outside xp 0 k b.mem t.mem := by
    intro q hq
    apply inv.frame q
    intro i hi eq
    subst q
    rw [show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hq
    omega_using [room, positive, size, bitsPositive, bitsBound, width, rbLength, bits, bytes, length, x, random, room256, maskA, maskHeaderA, subtract, ptrB, outB, indexB, skipB, onesB, zeroB, countB, valueT, hi, hq]
   obtain frameMask : Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem a.mem := outside_frame_member (ptr:=B) (k:=Z)
    (fun q h =>inscrA q (by omega_using [h])) (by simp)
   obtain frameOutput : Frame [⟨B,Z⟩,⟨xp,k⟩] a.mem t.mem := by
    rw [←memB];exact outside_frame_member outsideX (by simp)
   exact ⟨goodT,sampleDraw_bytes inv rbLength (by omega_using [positive, bitsPositive]),valueT,
    fun q hq =>(sameScratch q hq).trans (by rw [memA]),frameMask.trans frameOutput,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Connect immutable context import and policy sampling to the comb's initial state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ContextPrefix.lean`, which only this module imported.
section

/-! The canonical context contains exact, unreduced-width p and reduced R² limbs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_prefix {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 wv m ctx 24 w=P ∧ wv m ctx (24+8*w) w=2^(128*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 obtain countEq : count=3+34*w := context_words_count canonical
 obtain bound : P<2^(64*w) := by
  obtain h := os2ip_lt (dom.take k)
  obtain len : (dom.take k).length=k := by simp only [List.length_take];omega_using [length]
  rw [len,pow256_eq] at h
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega_using []))
 obtain positive : 0<P := by
  have h := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega_using [h]
 obtain prefixWords : Spec.Rsa.wordsAt m (off ctx 24) (2*w)=Spec.Rsa.toWords P w++Spec.Rsa.toWords (2^(128*w)%P) w := by
  obtain slice := VG.Proof.Mont.wordsAt_slice m ctx 0 count 3 (2*w) (by omega_using [countEq])
  obtain src := context_words length valid canonical
  simp only [VG.Proof.Mont.off,BitVec.add_zero,Nat.zero_add] at slice
  rw [src] at slice
  rw [VG.Proof.Ffdh.generationValues_montgomery] at slice
  exact slice.symm
 obtain values := pre_words prefixWords bound (Nat.lt_trans (Nat.mod_lt _ positive) bound)
 obtain zero : wv m (off ctx 24) 0 w=wv m ctx 24 w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.zero_add]
 obtain second : wv m (off ctx 24) (8*w) w=wv m ctx (24+8*w) w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.add_assoc]
 exact ⟨zero.symm.trans values.1,second.symm.trans values.2⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleFrame.lean`, which only this module imported.
section

/-! Sampling modifies the private output and its dedicated mask control only. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem sampleFrame_header {p : Parameters} {s t : State} {N i : Nat}
 (scratch : Scr s p.B p.Z) (inside : i<32) (different : i≠sMask)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 word t.mem p.B (8*i)=word s.mem p.B (8*i) := by
 rw [workspace_word (by have := scratch.nowrap;omega_using [this]) same
  (by have := hdr_lt_slot p.w 8 inside;have := p.room;omega_arith)]
 exact header_other (writeW_outside _ _ _ (by decide : 8*sMask+8≤2^64)) (by decide) inside different

theorem FieldInitial.after_sample {p : Parameters} {s t : State} {N : Nat}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) : FieldInitial p t := by
 obtain nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega_arith
 obtain masked := writeW_outside s.mem p.B (sampleMask N) (by decide : 8*sMask+8≤2^64)
 have arrays (a : Nat) (ha : a<8) : wv t.mem p.B (slot p.w a) p.w=wv s.mem p.B (slot p.w a) p.w := by
  obtain within := Nat.le_trans (slot_le (w:=p.w) ha) p.room
  apply Eq.trans _ (masked.wv (Or.inr (hdr_lt_slot p.w a (show sMask<32 by decide))) (by have := slot_le (w:=p.w) ha;omega_using [nowrap, this]))
  apply wv_congr
  intro i hi
  exact workspace_word (by have := field.good.scr.nowrap;omega_using [this]) same (by omega_using [within, hi])
 obtain wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  rw [workspace_word (by have := field.good.scr.nowrap;omega_using [this]) same
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.room;have := p.positive;omega_arith)]
  exact masked.word (Or.inr (hdr_lt_slot p.w 0 (show sMask<32 by decide)))
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.positive;omega_arith)
 refine ⟨good,(arrays 0 (by decide)).trans field.modulus,?_,(arrays 4 (by decide)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_sample {p : Parameters} {s t : State} {N k : Nat}
 (h : Controls p.B p.src p.ctx k p.N s) (scratch : Scr s p.B p.Z)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 Controls p.B p.src p.ctx k p.N t :=
 ⟨(sampleFrame_header scratch (by decide) (by decide) same).trans h.context,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.source,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.length,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.bits,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generateFront_ok {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (controls : Controls p.B p.src p.ctx p.k p.N s)
 (domain : word s.mem p.B (8*sDom)=dp) (domLen : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (y : word s.mem p.B (8*sY)=yp) (rand : word s.mem p.B (8*sRand)=rp)
 (bytes : word s.mem p.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8))
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i)) :
 WP isa (.seq importPrefix Generate.sample) s fun t =>
 ∃ mi,let q : Parameters := {p with mi:=mi}
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 Initial q bs t ∧ Spec.Rsa.os2ip bs=Spec.Rsa.os2ip rb%2^p.N ∧
 Src t p.B p.Z dp dom ∧ word t.mem p.B (8*sDom)=dp ∧
 word t.mem p.B (8*sDL)=BitVec.ofNat 64 dl ∧ word t.mem p.B (8*sY)=yp ∧ Keep mmRegs s t := by
 obtain domSize : p.k≤dom.length := by omega_using [shape, domLength]
 obtain validMod := VG.Proof.Ffdh.domainValid_mod valid
 obtain prefixValues := context_prefix domSize validMod view.canonical
 have wEq : p.w=Spec.Rsa.modulusWords p.k := words
 rw [←wEq,←modulus] at prefixValues
 obtain countEq : count=3+34*p.w := by rw [context_words_count view.canonical,←wEq]
 obtain odd : p.P%2=1 := by
  have h := validMod
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  rw [modulus];exact h.1.1.1
 rw [WP.seq_iff]
 refine WP.mono (importPrefix_ok scratch base p.room words positive size controls.length controls.context
  (fun i hi =>by
   obtain h := view.readable (3+i) (by omega_using [countEq, hi])
   simpa only [off,Nat.mul_add] using h)
  (fun i hi =>by
   obtain h := view.outside (24+i) (by omega_using [countEq, hi])
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using h)
  prefixValues.1 prefixValues.2 odd) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 obtain fieldA : FieldInitial q a := ⟨goodA,modulusA,inverseA,r2A⟩
 obtain inscrA : InScr p.B p.Z s.mem a.mem := InScr.of_frm frameA
  (fun r hr =>Nat.le_trans (importRanges_le _ r hr) p.room)
 obtain viewA := view.after_inscr inscrA restA
 obtain domainA := domainSource.congrK inscrA restA
 obtain randomA := randomSource.congrK inscrA restA
 have headerA (i : Nat) (lo : 16≤i) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) := importFrame_header frameA lo hi
 obtain controlsA : Controls q.B q.src q.ctx q.k q.N a :=
  ⟨(headerA sCtx (by decide) (by decide)).trans controls.context,
   (headerA sX (by decide) (by decide)).trans controls.source,
   (headerA sLen (by decide) (by decide)).trans controls.length,
   (headerA sBits (by decide) (by decide)).trans controls.bits,
   (headerA sRows (by decide) (by decide)).trans controls.rows⟩
 refine WP.mono (sample_ok goodA p.room positive size bitsPositive bitsBound width rbLength controlsA.bits
  ((headerA sBytes (by decide) (by decide)).trans bytes) controlsA.length controlsA.source
  ((headerA sRand (by decide) (by decide)).trans rand) randomA
  (fun i hi =>by rw [restA.wr];exact writeX i hi) outsideX separateRand) ?_
 rintro t ⟨goodT,_,valueT,sameT,frameT,restT⟩
 obtain total : Keep mmRegs s t := (restA.trans restT).mono (by simp [mmRegs])
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 obtain bsLength : bs.length=p.k := by simp only [bs,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 obtain fieldT := fieldA.after_sample goodT sameT
 obtain controlsT := controlsA.after_sample goodA.scr sameT
 obtain viewT := viewA.after_output frameT restT separateContext
 obtain domainT := src_after_output domainA frameT restT separateDomain
 obtain actual : Source q.src bs t := source_of_bytesAt t p.src p.k (fun i hi =>by
  obtain ⟨r,hr,contains⟩ := writeX i hi
  exact ⟨r,List.mem_append_right _ (by rw [total.wr];exact hr),contains⟩)
 obtain readsT : ReadEnv q bs t := context_readEnv wEq modulus generator policy table domSize validMod viewT.canonical
  actual bsLength (fun i hi =>outsideX i (by omega_using [bsLength, hi])) viewT.readable viewT.outside
 have headerT (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠sMask) : word t.mem p.B (8*i)=word s.mem p.B (8*i) :=
  (sampleFrame_header (p:=q) goodA.scr hi different sameT).trans (headerA i lo hi)
 refine ⟨mi,⟨fieldT,?_,readsT⟩,valueT,domainT,?_,?_,?_,total⟩
 · change Controls q.B q.src q.ctx bs.length q.N t
   rw [bsLength]
   exact controlsT
 · exact (headerT sDom (by decide) (by decide) (by decide)).trans domain
 · exact (headerT sDL (by decide) (by decide) (by decide)).trans domLen
 · exact (headerT sY (by decide) (by decide) (by decide)).trans y

end VG.Proof.Ffdh.AArch64.Cached
