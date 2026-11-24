module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Joined
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Finish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # Produce the full POWER tag from the joined ciphertext and GHASH -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag j0)
open VG.Proof.Gcm (padA)
open VG.Proof.AesGcm.PPC64LE.DirectGather (tagLengths tagLengths_wp padded_whole)

abbrev tagWrites (s : State) := tagFrame (s.gpr .r30) (s.gpr .r31) 0

structure Tagged (s t : State) (H : Block) (iv a : List Byte) : Prop where
  sp : t.sp=s.sp
  regs : ∀ r∈savedEnd,t.gpr r=s.gpr r
  data : bytesAt t.mem (s.gpr .r27) (datLen s)=Proof.Gcm.xorKs (ctxCiph s.mem (s.gpr .r29) (roundsOf s)) (Spec.Gcm.inc32 (j0 H iv)) 0 (bytesAt s.mem (s.gpr .r19) (datLen s))
  tag : bytesAt t.mem (s.gpr .r31) 16=fullTag (ctxCiph s.mem (s.gpr .r29) (roundsOf s)) H iv a (bytesAt t.mem (s.gpr .r27) (datLen s))
  frame : Frame (cipherFrame s++tagWrites s) s.mem t.mem

theorem tagAfter_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s u : State} {H : Block} {iv a : List Byte}
    (p : CoreIn s) (q : Joined s u H (Spec.Gcm.inc32 (j0 H iv)) (padA a))
    (rd : u.rd=s.rd) (wr : u.wr=s.wr)
    (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14)
    (ad : (s.gpr .r22).toNat=a.length) (hash : ctxH s.mem (s.gpr .r29)=H) (j : blockAt s.mem (s.gpr .r30)=j0 H iv)
    (ctx : ∀ r∈cipherFrame s,(ctxRegion s).Disjoint r)
    (ctr : ∀ r∈cipherFrame s,(⟨s.gpr .r30,16⟩ : Region).Disjoint r)
    (dst : ∀ r∈tagWrites s,(dat s).Disjoint r) :
    WP isa (.seq (.block tagLengths) (VG.Impl.AesGcm.PPC64LE.tag 0)) u (fun t => Tagged s t H iv a) := by
  have c := q.regs .r29 (by decide)
  have st := q.regs .r30 (by decide)
  have w := q.regs .r31 (by decide)
  have r := q.regs .r28 (by decide)
  have env : Env u.gpr s.sp u := ⟨fun _ _ => rfl,q.sp,by rw [c,st,w];exact p.perm.of_eq rd wr⟩
  have h := (ctxH_keep q.frame ctx).trans hash
  have jj := (blockAt_frame q.frame ctr).trans j
  let ct := bytesAt u.mem (s.gpr .r27) (datLen s)
  have auth := q.auth
  change Auth (s.gpr .r30) H (padA a++ct++_) u at auth
  rw [padded_whole] at auth
  have y := auth.whole_eq (Proof.Gcm.length_padded a ct)
  refine WP.seq (WP.mono (tagLengths_wp env) fun z ⟨l1,l2,ze,keep⟩ => ?_)
  refine WP.mono (tag_ok (p.layout.v c st w) (o := 0) (.inl rfl) ze (R := roundsOf s) (by simp [r,roundsOf]) R
    (H := H) (by rw [keep.mem,c];exact h) (J := j0 H iv) (by rw [keep.mem,st];exact jj)) fun t out => ?_
  have fr := out.frame
  rw [keep.mem,st,w] at fr
  have text : bytesAt t.mem (s.gpr .r27) (datLen s)=ct := bytesAt_frame fr dst (Nat.le_of_lt p.bounds.src.lt)
  refine ⟨out.env.sp,?_,text.trans q.data,?_,(q.frame.mono fun _ e => List.mem_append_left _ e).trans (fr.mono fun _ e => List.mem_append_right _ e)⟩
  · intro reg er
    exact (out.env.fr reg (by revert reg;decide)).trans (q.regs reg er)
  · have got := out.out
    have len : ct.length=datLen s := length_bytesAt ..
    rw [w,BitVec.add_zero,l1,l2,q.regs .r22 (by decide),q.regs .r23 (by decide),ad,keep.mem,c,st,y,ciph_frame q.frame ctx R] at got
    rw [text,Proof.Gcm.fullTag_eq,len]
    exact got

/-- The whole contiguous payload, including GHASH padding, the lengths block, and the final tag mask. -/
theorem payload_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} {H : Block} {iv a : List Byte} (p : CoreIn s) (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14)
    (cipher : Proof.Gcm.Ctr s.mem (s.gpr .r30+48) (s.gpr .r30+64) (ctxCiph s.mem (s.gpr .r29) (roundsOf s)) (Spec.Gcm.inc32 (j0 H iv)) 0)
    (auth : Auth (s.gpr .r30) H (padA a) s) (ad : (s.gpr .r22).toNat=a.length)
    (hash : ctxH s.mem (s.gpr .r29)=H) (j : blockAt s.mem (s.gpr .r30)=j0 H iv)
    (ctx : ∀ r∈cipherFrame s,(ctxRegion s).Disjoint r)
    (ctr : ∀ r∈cipherFrame s,(⟨s.gpr .r30,16⟩ : Region).Disjoint r)
    (dst : ∀ r∈tagWrites s,(dat s).Disjoint r) :
    WP isa VG.Impl.AesGcm.PPC64LE.Contiguous.payload s (fun t => Tagged s t H iv a) := by
  have xa : (padA a).length%16=0 := Proof.Gcm.length_padA_mod a
  have h := WP.seq (WP.mono (WP.with_rdwr (cipher_wp p R cipher auth xa hash)) fun u ⟨q,rd,wr,_⟩ =>
    tagAfter_wp p q rd wr R ad hash j ctx ctr dst)
  obtain ⟨_,_,ex,result⟩ := h
  cases ex with
  | seq eabc ed => cases eabc with
    | seq eab ec => cases eab with
      | seq ea eb => exact ⟨_,_,.seq ea (.seq eb (.seq ec ed)),result⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous
