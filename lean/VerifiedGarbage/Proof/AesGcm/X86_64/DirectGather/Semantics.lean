module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Quick
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.DirectFinish
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Relate the ciphertext and authentication state across the first slice and the final two tails. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather Gather.DirectTail Short
open VG.Spec.Gcm (Block ctxH ctxCiph j0 inc32 blockAt gctr toBytes ghash ghashFrom blocks padLen zeros ofBytes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs lensBlock padded)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

theorem auth_suffix (H : Block) (a c t : List Byte) (hc : c.length % 16 = 0) (ht : t.length ≤ 16) :
    ghashFrom H (ghashFrom H (ghash H (blocks (a ++ zeros (padLen a.length)))) (blocks c))
      ((if t.length = 0 then [] else [ofBytes (t ++ zeros (16 - t.length))]) ++
        [ofBytes (lensBlock a.length (c.length+t.length))]) =
    ghashFrom H (ghash H (blocks (padded a (c++t)))) [ofBytes (lensBlock a.length (c++t).length)] := by
  have hA : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hAC : (a ++ zeros (padLen a.length) ++ c).length % 16 = 0 := by rw [List.length_append]; omega
  rw [Proof.Gcm.ghashFrom_append]
  rw [List.length_append]
  apply congrArg (fun y => ghashFrom H y [ofBytes (lensBlock a.length (c.length+t.length))])
  rw [← padded_eq]
  by_cases z : t.length=0
  · have e := List.eq_nil_of_length_eq_zero z
    subst t
    simp only [List.length_nil,ite_true,List.append_nil,Proof.Gcm.ghashFrom_nil,Proof.Gcm.padLen_of_mod hAC]
    change _ = ghash H (blocks (a ++ zeros (padLen a.length) ++ c ++ []))
    rw [List.append_nil, Proof.Gcm.blocks_append hA]
    simp only [ghash, Proof.Gcm.ghashFrom_append]
  · have p : padLen (a ++ zeros (padLen a.length) ++ (c++t)).length = 16 - t.length := by
      simp only [padLen, List.length_append, Proof.Gcm.length_zeros] at hA ⊢
      omega
    simp only [z, ↓reduceIte, p]
    have assoc : a ++ zeros (padLen a.length) ++ (c ++ t) ++ zeros (16-t.length) =
        (a ++ zeros (padLen a.length) ++ c) ++ (t ++ zeros (16-t.length)) := by simp only [List.append_assoc]
    rw [assoc, Proof.Gcm.blocks_append hAC, Proof.Gcm.blocks_single (bs := t ++ zeros (16-t.length)) (by rw [List.length_append,Proof.Gcm.length_zeros]; omega),
      Proof.Gcm.blocks_append hA]
    simp only [ghash, Proof.Gcm.ghashFrom_append]

theorem cipher_suffix (a : TailArgs) (ciph : Block → Block) (icb : Block) (m : Mem)
    (le : a.firstLen ≤ a.len) (bound : a.remaining ≤ 16)
    (key : blockAt m (a.work+1040#64) = ciph (Nat.repeat inc32 (a.firstLen/16) icb)) :
    a.cipherBytes m = xorKs ciph icb a.consumed (a.textBytes m) := by
  have len : (a.textBytes m).length=a.remaining := by
    simp only [TailArgs.textBytes, List.length_append, length_bytesAt, TailArgs.remaining,TailArgs.consumed,TailArgs.secondLen]
    omega
  apply Proof.Gcm.zipWith_eq_xorKs (by rw [length_bytesAt,len])
  intro i hi
  rw [len] at hi
  rw [Proof.Gcm.getD_bytesAt' _ _ hi,Proof.Gcm.bytes_toBytes_blockAt m _ (k := i) (by omega),key,Proof.Gcm.ksByte]
  have d : (a.consumed+i)/16=a.firstLen/16 := by change (16*(a.firstLen/16)+i)/16=_; omega
  have r : (a.consumed+i)%16=i := by change (16*(a.firstLen/16)+i)%16=_; omega
  rw [d,r]

theorem first_slots_frame (m : Mem) (W S D : Addr) (n : Nat) :
    Frame [⟨W+192#64,40⟩] m (firstMem m W S D n) := by
  have slot (d : Nat) (lo : 192≤d) (hi : d+8≤232) :
      (⟨W+192#64,40⟩ : Region).Contains (W+BitVec.ofNat 64 d) 8 :=
    Offset.contains W lo hi (by omega)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) S (slot 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) D (slot 200 (by decide) (by decide))).writeW (List.mem_singleton_self _)
    (BitVec.ofNat 64 n) (slot 192 (by decide) (by decide))

theorem first_block {m : Mem} {W S D : Addr} {n d : Nat} (hi : d+16≤192) :
    blockAt (firstMem m W S D n) (W+BitVec.ofNat 64 d)=blockAt m (W+BitVec.ofNat 64 d) :=
  blockAt_frame (first_slots_frame m W S D n) (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r; exact Offset.disjoint W (.inl hi) (by omega) (by decide))

namespace Layout
variable {M : CtxMode} {s : State} (h : Layout M s)
include h

theorem ctx_framed {m : Mem} (fr : Frame (changed s) s.mem m) {R : Nat} (le : R≤14) :
    ctxH m (K s)=ctxH s.mem (K s) ∧ ctxCiph m (K s) R=ctxCiph s.mem (K s) R := by
  have read {p : Addr} {n : Nat} (sub : (⟨p,n⟩ : Region).Sub ⟨K s,256⟩) (bound : n≤256) :
      bytesAt m p n=bytesAt s.mem p n := bytesAt_frame fr (fun r hr =>
        (h.ext_apart r hr).sub_left (fun a hit => Region.sub_prefix M.ge a (sub a hit))) (by omega)
  constructor
  · rw [ctxH_eq,ctxH_eq,blockAt,blockAt,read (Lay.ctxSub (by decide)) (by decide)]
  · simp only [ctxCiph]
    rw [read (Region.sub_prefix (by omega)) (by omega)]

theorem prefix_text {m : Mem} (fr : Frame (changed s) s.mem m) (cnt : Cnt s=1 ∨ Cnt s=2) :
    pt s (Cnt s)=bytesAt m (sb s 0) (tailArgs s).consumed ++ (tailArgs s).textBytes m := by
  have nz : 0<Cnt s := by omega
  have split : (tailArgs s).consumed + sl s 0%16=sl s 0 := by
    change 16*(sl s 0/16)+sl s 0%16=_; omega
  have first := bytesAt_frame fr (h.slice_apart nz) (Nat.le_of_lt (BitVec.isLt _))
  change bytesAt m (sb s 0) (sl s 0)=_ at first
  have b := bytesAt_add m (sb s 0) (tailArgs s).consumed (sl s 0%16)
  rw [split,first] at b
  have z : pt s 0=[] := rfl
  have gl := h.glen
  simp only [TailArgs.textBytes,tailArgs,TailArgs.tail1,TailArgs.secondLen] at b ⊢
  rw [←List.append_assoc,←b]
  rcases cnt with one|two
  · rw [one,pt_succ,z,List.nil_append]
    rw [one,gl_succ,gl_zero,Nat.zero_add] at gl
    simp [←gl,bytesAt]
  · rw [two,pt_succ,pt_succ,z,List.nil_append]
    rw [two,gl_succ,gl_succ,gl_zero,Nat.zero_add] at gl
    have second := bytesAt_frame fr (h.slice_apart (show 1<Cnt s by omega)) (Nat.le_of_lt (BitVec.isLt _))
    change bytesAt m (sb s 1) (sl s 1)=_ at second
    simp only [show (1:Nat)<2 by decide,ite_true]
    rw [show L s-sl s 0=sl s 1 by omega,second]

abbrev qSrc (s : State) := bytesAt s.mem (sb s 0) (tailArgs s).consumed
abbrev qDst (s v : State) := bytesAt v.mem (Dst s) (tailArgs s).consumed
abbrev qIv (s : State) := bytesAt s.mem (Nn s) 12
abbrev qAad (s : State) := bytesAt s.mem (Ad s) (AL s).toNat
abbrev qH (s : State) := ctxH s.mem (K s)
abbrev qCiph (s : State) := ctxCiph s.mem (K s) (s.gpr .rsi).toNat
abbrev qJ (s : State) := j0 (qH s) (qIv s)

theorem whole_summary {u m v : State} (nz : 0<Cnt s) (whole : WholeDone s u m v) :
    qDst s v = xorKs (qCiph s) (inc32 (qJ s)) 0 (qSrc s) ∧
    blockAt v.mem (Split.cbA (W s)) = Nat.repeat inc32 (sl s 0/16) (inc32 (qJ s)) ∧
    blockAt v.mem (Split.yA (W s)) = ghashFrom (qH s)
      (ghash (qH s) (blocks (qAad s ++ zeros (padLen (qAad s).length)))) (blocks (qDst s v)) ∧
    blockAt v.mem (W s+16#64) = qJ s ∧ SavedAt v.mem (W s) s := by
  obtain ⟨mid,out⟩ := whole
  let m' := firstMem m.mem (W s) (sb s 0) (Dst s) (L s)
  have f₀ : Frame (changed s) s.mem m.mem := mid.frame.sub (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ hit => hit⟩
    · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩)
  have f₁ := first_slots_frame m.mem (W s) (sb s 0) (Dst s) (L s)
  have f : Frame (changed s) s.mem m' := f₀.trans (f₁.sub (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r; exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩))
  have le : (s.gpr .rsi).toNat≤14 := by omega_using [h.rounds]
  obtain ⟨hh,hc⟩ := h.ctx_framed f le
  have cb : blockAt m' (Split.cbA (W s))=inc32 (qJ s) := by
    have b := mid.cb; simp only [add_ofNat_ofNat] at b
    simpa only [Split.cbA,add_ofNat_ofNat] using (first_block (m:=m.mem) (S:=sb s 0) (D:=Dst s) (n:=L s) (d:=64) (by decide)).trans b
  have y : blockAt m' (Split.yA (W s))=ghash (qH s) (blocks (qAad s ++ zeros (padLen (qAad s).length))) := by
    have b := mid.abs.whole_eq (by rw [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    simp only [add_ofNat_ofNat] at b
    simpa only [Split.yA,add_ofNat_ofNat] using (first_block (m:=m.mem) (S:=sb s 0) (D:=Dst s) (n:=L s) (d:=32) (by decide)).trans b
  have cnt : sl s 0≤L s := (h.inputs mid nz).sl_le
  have leBytes : (tailArgs s).consumed≤sl s 0 := Nat.mul_div_le ..
  have src := bytesAt_frame (p:=sb s 0) (n:=(tailArgs s).consumed) f
    (fun r hr => (h.slice_apart nz r hr).sub_left (Region.sub_prefix leBytes)) (by omega_using [leBytes,show sl s 0<2^64 from BitVec.isLt _])
  have c := (Proof.Gcm.ctr_wholeTo (m:=m') (m':=v.mem) (cb:=Split.cbA (W s)) (ks:=W s) (sp:=sb s 0) (dp:=Dst s)
    (ciph:=ctxCiph m' (K s) (s.gpr .rsi).toNat) (icb:=blockAt m' (Split.cbA (W s))) (n:=0) (nb:=sl s 0/16)
    ⟨rfl,fun h => (h rfl).elim⟩ rfl out.blocks out.ctr).1
  have ctr := out.ctr
  change blockAt v.mem _=Nat.repeat inc32 _ (blockAt m' _) at ctr
  have hash := out.y
  change blockAt v.mem _=ghashFrom (ctxH m' _) (blockAt m' _) _ at hash
  rw [hc,cb] at c
  change qDst s v=xorKs (qCiph s) _ 0 (bytesAt m' _ (tailArgs s).consumed) at c
  rw [src] at c
  rw [hh,y,Proof.Gcm.blocksAt_eq] at hash
  rw [cb] at ctr
  have apart {d n : Nat} (range : d+n≤32 ∨ (128≤d ∧ d+n≤192)) :
      ∀ r ∈ Split.callWr (W s) (Dst s) (sl s 0/16) ++ [below (SP s) 56],
      (⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr
    have sub : (⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Sub ⟨W s,2560⟩ := Lay.wSub (by omega)
    simp only [Split.callWr,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,add_ofNat_ofNat] at hr
    rcases hr with (rfl|rfl|rfl|rfl)|rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
    · exact (h.d_w.symm.sub_left sub).sub_right (Region.sub_prefix (by change sl s 0/16*16≤L s; omega))
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
    · exact ((h.b_w.sub_left (below_sub (by decide) (by decide))).symm).sub_left sub
  refine ⟨c,ctr,hash,(blockAt_frame out.frame (apart (d:=16) (n:=16) (.inl (by decide)))).trans
    ((first_block (d:=16) (by decide)).trans mid.j0),?_⟩
  apply SavedAt.frame (mid.saved.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))) out.frame
  exact apart (.inr ⟨by decide,by decide⟩)

end Layout
end VG.Proof.AesGcm.X86_64.DirectGather
