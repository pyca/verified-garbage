module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.TextDone
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Iteration
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Setup
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.LoopTiming

@[expose] public section

/-! Authenticate the directly written ciphertext, retaining the hash of any fused prefix. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Impl.AesGcm.X86_64 (oneTag)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros padLen blockAt)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

namespace TextDone
variable {M : CtxMode} {s t : State} {pre : Nat} (h : Layout M s) (d : TextDone M s t pre)
include h d

theorem tag_input : OneT (K s) (W s) (SP s) (R s) (AL s).toNat (Dst s+BitVec.ofNat 64 pre) (L s-pre) (L s) t :=
  ⟨d.env,d.rounds,by simpa only [ofNat_toNat] using d.aad,d.data,d.len,
   (((h.oneCtx M.ge).data.of_eq d.rd d.wr).drop d.prefix).ok,d.total⟩

theorem tag_wp (v : GcmImpl) : WP isa (oneTag v.callees 0) t (BodyDone M s) := by
  have c := h.oneCtx M.ge
  have p := d.tag_input h
  have xa : (ad s ++ zeros (padLen (ad s).length) ++ bytesAt t.mem (Dst s) pre).length%16=0 := by
    simp only [List.length_append,length_bytesAt,Proof.Gcm.length_zeros]
    exact Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_add (Nat.dvd_iff_mod_eq_zero.mpr (Proof.Gcm.length_pad_mod _)) (Nat.dvd_iff_mod_eq_zero.mpr d.aligned))
  have half := (h.d_w.sub_left (Offset.sub_base (Dst s) (d:=pre) (n:=L s-pre) (by omega_using [d.prefix])))
  refine WP.mono (oneTag_ok v c.lay (o:=0) (.inl rfl) xa p.env d.hkey p.rounds p.dat p.len p.tlen
    (BitVec.isLt _) p.alen p.dD half) fun u ⟨env,f,rd,wr,_,_,tag⟩ => ?_
  have tg := tag d.auth
  have df := h.b_d.sub_left (below_sub (a:=8) (by decide) (by decide))
  have cipher : bytesAt u.mem (Dst s) (L s)=bytesAt t.mem (Dst s) (L s) := bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact h.d_w.sub_right (Lay.wSub (by decide))
    · exact h.d_w.sub_right (Lay.wSub (by decide))
    · exact h.d_w.sub_right (Lay.wSub (by decide))
    · exact h.d_w.sub_right (Lay.wSub (by decide))
    · exact df.symm) (Nat.le_of_lt (BitVec.isLt _))
  have fs : Frame (changed s) t.mem u.mem := f.sub (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact ⟨⟨W s,2560⟩,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨⟨W s,2560⟩,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨⟨W s,2560⟩,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨⟨W s,2560⟩,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩)
  refine ⟨env,rd.trans d.rd,wr.trans d.wr,d.saved.frame f ?_,d.frame.trans fs,cipher.trans d.cipher,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact ((h.b_w.sub_left (below_sub (by decide) (by decide))).symm).sub_left (Lay.wSub (by decide))
  · have sum : pre+(L s-pre)=L s := Nat.add_sub_of_le d.prefix
    have full := bytesAt_add t.mem (Dst s) pre (L s-pre)
    rw [sum] at full
    have eq : ad s ++ zeros (padLen (ad s).length) ++ bytesAt t.mem (Dst s) pre ++
        bytesAt t.mem (Dst s+BitVec.ofNat 64 pre) (L s-pre)=ad s ++ zeros (padLen (ad s).length) ++ bytesAt u.mem (Dst s) (L s) := by
      rw [cipher,full,List.append_assoc]
    rw [eq,padded_eq,d.key,d.j0,BitVec.add_zero] at tg
    rw [Proof.Gcm.fullTag_eq]
    simpa only [ad,length_bytesAt] using tg

theorem tag_rel (v : GcmImpl) {s' t' : State} (q : Layout M s') (pb : Pub s s') (b : TextDone M s' t' pre) :
    RelCT isa (fun x y => x=t ∧ y=t') (oneTag v.callees 0) fun _ _ => True := by
  have c := h.oneCtx M.ge
  have half := h.d_w.sub_left (Offset.sub_base (Dst s) (d:=pre) (n:=L s-pre) (by omega_using [d.prefix]))
  refine (oneTag_relT v c.lay (o:=0) (R:=R s) (al:=(AL s).toNat) (N:=L s) (.inl rfl) half).mono ?_ (fun _ _ _ => trivial)
  rintro x y ⟨rfl,rfl⟩
  exact ⟨d.tag_input h, by simpa only [K,SP,R,AL,pb.rdi,pb.rsp,pb.rsi,pb.r9,pb.eL,pb.w,pb.dst] using b.tag_input q⟩

end TextDone
end VG.Proof.AesGcm.X86_64.DirectGather

/-! Encrypt all descriptors in their original order and authenticate the remaining ciphertext. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {M : CtxMode} {s t : State} {pre : Nat}

theorem loop_ok (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) (h : Layout M s)
    (a : LoopAt M s pre 0 t) (hn : 0<Cnt s) :
    WP isa (.loop (iteration v c) .ne) t (LoopAt M s pre (Cnt s)) := by
  refine WP.loop (M:=isa) (body:=iteration v c) (c:=.ne) (fun (n : Nat) (z : State) => ∃ i,i<Cnt s ∧ n=Cnt s-i ∧ LoopAt M s pre i z)
    (fun n z ⟨i,hi,nEq,atI⟩ => (iteration_ok v c h atI hi).mono fun z' ⟨next,zero⟩ => ?_)
    (Cnt s) t ⟨0,hn,rfl,a⟩
  by_cases e : Cnt s-(i+1)=0
  · exact .inl ⟨by simp [eval,zero,e],(show i+1=Cnt s by omega) ▸ next⟩
  · exact .inr ⟨by simp [eval,zero,e],Cnt s-(i+1),by omega,i+1,by omega,rfl,next⟩

def prefixBytes (f : Option Fn) (s : State) :=
  if Cnt s=0 then 0 else if f.isSome then 256*(sl s 0/256) else 0

abbrev prefixProgram (f : Option Fn) : Prog isa := (f.map bulk).getD (.block [])

abbrev PrefixWP (M : CtxMode) (f : Option Fn) : Prop := ∀ {s t : State}, Layout M s →
  LoopAt M s 0 0 t → 0<Cnt s → WP isa (prefixProgram f) t (LoopAt M s (prefixBytes f s) 0)

theorem plainPrefix_wp : PrefixWP M none := by
  intro s t _ a _
  simpa [prefixBytes,prefixProgram] using (WP.block_nil (M:=isa) (s:=t) a)

theorem pieces_wp (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) {f : Option Fn} (bc : PrefixWP M f)
    (h : Layout M s) {u : State} (a : GeneralAad s u t) :
    WP isa (pieces v.callees ⟨c.callee.name,c.callee.code⟩ f) t (fun z => TextDone M s z (prefixBytes f s)) := by
  refine WP.seq ((setup_wp h a).mono fun p ⟨inp,zero⟩ => ?_)
  refine WP.ite (decide (Cnt s=0)) zero (fun hz => ?_) (fun hz => ?_)
  · have z : Cnt s=0 := by simpa using hz
    have e : LoopAt M s 0 (Cnt s) p := z ▸ inp
    exact WP.block_nil (by simpa [prefixBytes,z] using e.done h)
  · have ne : Cnt s≠0 := by simpa using hz
    refine WP.seq ((bc h inp (by omega)).mono fun p' v' =>
      (loop_ok v c h v' (by omega)).mono fun _ o => o.done h)

theorem general_wp (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) {f : Option Fn} (bc : PrefixWP M f)
    (h : Layout M s) (e : Layout.Initial s t) :
    WP isa (general v.callees ⟨c.callee.name,c.callee.code⟩ f) t (BodyDone M s) :=
  WP.seq ((general_aad_wp v h e).mono fun _ a => WP.seq ((pieces_wp v c bc h a).mono
    fun _ d => d.tag_wp h v))

end VG.Proof.AesGcm.X86_64.DirectGather

/-! The timing proof for encryption directly from an arbitrary descriptor list. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_ite rel_skip)
variable {M : CtxMode} {s t x y : State}

theorem prefixBytes_eq (f : Option Fn) (p : Pub s t) : prefixBytes f t=prefixBytes f s := by
  by_cases z : Cnt s=0
  · simp [prefixBytes,p.cnt,z]
  · simp [prefixBytes,p.cnt,z,p.sl (show 0<Cnt s by omega)]

abbrev PrefixCT (M : CtxMode) (f : Option Fn) := ∀ {s t x y : State},Layout M s → Layout M t → Pub s t →
  LoopAt M s 0 0 x → LoopAt M t 0 0 y → 0<Cnt s → RelCT isa (Eq2 x y) (prefixProgram f) TT

theorem plainPrefix_rel : PrefixCT M none := fun _ _ _ _ _ _ => rel_skip

theorem pieces_rel (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) {f : Option Fn}
    (wp : PrefixWP M f) (ct : PrefixCT M f) (h : Layout M s) (k : Layout M t) (pub : Pub s t)
    {a b : State} (p : GeneralAad s a x) (q : GeneralAad t b y) :
    RelCT isa (Eq2 x y) (pieces v.callees ⟨c.callee.name,c.callee.code⟩ f) TT := by
  have setup := (setup_rel (u:=a) (v:=b) pub).mono (P':=Eq2 x y) (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨p,q⟩) (fun _ _ z => z)
  apply rel_seq setup (setup_wp h p) (setup_wp k q)
  rintro u z ⟨a,za⟩ ⟨b,zb⟩
  rw [pub.cnt] at zb
  refine rel_ite (b:=decide (Cnt s=0)) za zb (fun _ => rel_skip) (fun ne => ?_)
  have pos : 0<Cnt s := Nat.pos_of_ne_zero (by simpa using ne)
  apply rel_seq (ct h k pub a b pos) (wp h a pos) (wp k b (pub.cnt ▸ pos))
  intro u' z' lu lz
  rw [prefixBytes_eq f pub] at lz
  exact loop_rel v c h k pub pos lu lz

theorem general_rel (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) {f : Option Fn}
    (wp : PrefixWP M f) (ct : PrefixCT M f) (h : Layout M s) (k : Layout M t) (pub : Pub s t)
    (p : Layout.Initial s x) (q : Layout.Initial t y) :
    RelCT isa (Eq2 x y) (general v.callees ⟨c.callee.name,c.callee.code⟩ f) TT := by
  apply rel_seq ((general_aad_rel v h k pub).mono (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨p,q⟩) (fun _ _ z => z))
    (general_aad_wp v h p) (general_aad_wp v k q)
  intro a b u z
  apply rel_seq (pieces_rel v c wp ct h k pub u z) (pieces_wp v c wp h u) (pieces_wp v c wp k z)
  intro a' b' left right
  rw [prefixBytes_eq f pub] at right
  exact left.tag_rel h v k pub right

end VG.Proof.AesGcm.X86_64.DirectGather
