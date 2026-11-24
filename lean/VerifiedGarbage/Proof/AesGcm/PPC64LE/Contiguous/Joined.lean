module

-- separate module: The source suffix must survive prefix writes when plaintext and ciphertext share an address.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.PrefixMath
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Rest
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.Offset

/-! # Joining the fused and residual POWER seal ciphertext intervals -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.PPC64LE.DirectGather (cursors Range prefixLen prefixBlocks prefixLe prefixEq)

abbrev datLen (s : State) := (s.gpr .r23).toNat
abbrev datPrefix (s : State) := prefixLen (datLen s)
abbrev dat (s : State) : Region := ⟨s.gpr .r27,datLen s⟩
abbrev srcRegion (s : State) : Region := ⟨s.gpr .r19,datLen s⟩
abbrev ctxRegion (s : State) : Region := ⟨s.gpr .r29,256⟩
abbrev slab (s : State) : Region := ⟨s.gpr .r31+448,704⟩
abbrev prefixR (s : State) : Region := ⟨s.gpr .r27,datPrefix s⟩
abbrev restR (s : State) : Region := ⟨s.gpr .r27+BitVec.ofNat 64 (datPrefix s),datLen s-datPrefix s⟩
abbrev savedEnd : List Reg := [.r2,.r14,.r15,.r16,.r17,.r20,.r22,.r23,.r27,.r28,.r29,.r30,.r31]
abbrev cipherFrame (s : State) := prefixAreas s (datPrefix s) ++
  (crFrame (s.gpr .r30) (s.gpr .r31) (restR s).base (restR s).len ++ taFrame (s.gpr .r30) (s.gpr .r31))

structure CoreIn (s : State) : Prop where
  perm : Perm (s.gpr .r29) (s.gpr .r30) (s.gpr .r31) s
  layout : Lay (s.gpr .r29) (s.gpr .r30) (s.gpr .r31)
  bounds : Range s.gpr s (s.gpr .r19) (s.gpr .r27) (datLen s)
  slabSrc : (srcRegion s).Disjoint (slab s)
  slabDst : (dat s).Disjoint (slab s)
  slabCtx : (ctxRegion s).Disjoint (slab s)
  access : FusedAccess s
  read : Covers (fusedRead s++fusedWrite s) (s.rd++s.wr)
  write : Covers (fusedWrite s) s.wr

abbrev Auth (st : Addr) (H : Block) (x : List Byte) (t : State) :=
  Absorbed t.mem (st+BitVec.ofNat 64 16) (st+BitVec.ofNat 64 32) H x

abbrev paddedTail (x d : List Byte) := (x++d)++zeros (padLen (x++d).length)

structure Joined (s t : State) (H icb : Block) (x : List Byte) : Prop where
  sp : t.sp=s.sp
  regs : ∀ r∈savedEnd,t.gpr r=s.gpr r
  data : bytesAt t.mem (s.gpr .r27) (datLen s)=xorKs (ctxCiph s.mem (s.gpr .r29) (s.gpr .r28).toNat) icb 0
    (bytesAt s.mem (s.gpr .r19) (datLen s))
  auth : Auth (s.gpr .r30) H (paddedTail x (bytesAt t.mem (s.gpr .r27) (datLen s))) t
  frame : Frame (cipherFrame s) s.mem t.mem

private theorem behind {s : State} {r : Region} (st : r.Disjoint ⟨s.gpr .r30,80⟩) (scratch : r.Disjoint (slab s))
    (dst : r.Disjoint (prefixR s)) : ∀ q ∈ prefixAreas s (datPrefix s),r.Disjoint q := by
  intro q h
  simp only [prefixAreas,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact st.sub_right (Lay.stSub (by decide))
  · exact st.sub_right (Lay.stSub (by decide))
  · exact dst
  · exact scratch

private theorem srcAfter {s t : State} (p : CoreIn s) (f : Frame (prefixAreas s (datPrefix s)) s.mem t.mem) :
    let k := datPrefix s
    bytesAt t.mem (s.gpr .r19+BitVec.ofNat 64 k) (datLen s-k)=bytesAt s.mem (s.gpr .r19+BitVec.ofNat 64 k) (datLen s-k) := by
  let n := datLen s
  let k := datPrefix s
  have fit : k ≤ n := prefixLe n
  have sub : (⟨s.gpr .r19+BitVec.ofNat 64 k,n-k⟩ : Region).Sub (srcRegion s) := Offset.sub_base _ (Nat.le_of_eq (Nat.add_sub_of_le fit))
  apply bytesAt_frame f (behind (p.bounds.src.st.sub_left sub) (p.slabSrc.sub_left sub) ?_) (Nat.le_trans (Nat.sub_le n k) (Nat.le_of_lt (s.gpr .r23).isLt))
  rcases p.bounds.buffers with eq|apart
  · change Region.Disjoint ⟨s.gpr .r19+BitVec.ofNat 64 k,n-k⟩ ⟨s.gpr .r27,k⟩
    rw [eq];exact (split_disj fit p.bounds.src.lt).symm
  · exact (apart.sub_left sub).sub_right (Region.sub_prefix fit)

private theorem prefixAfter {s u t : State} (p : CoreIn s) (q : PrefixResult s u)
    (f : Frame (crFrame (u.gpr .r30) (u.gpr .r31) (u.gpr .r18) (restR s).len++taFrame (u.gpr .r30) (u.gpr .r31)) u.mem t.mem) :
    bytesAt t.mem (s.gpr .r27) (datPrefix s)=bytesAt u.mem (s.gpr .r27) (datPrefix s) := by
  rw [q.saved .r30 (by decide),q.saved .r31 (by decide),q.dst] at f
  have part := p.bounds.dst.take (prefixLe (datLen s))
  apply bytesAt_frame f (fun r hr => ?_) (Nat.le_of_lt part.ok.lt)
  rcases List.mem_append.mp hr with er|er
  · simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at er
    rcases er with rfl|rfl
    · exact split_disj (prefixLe _) p.bounds.src.lt
    · exact part.ok.st.sub_right (Lay.stSub (by decide))
  · exact data_taFrame part.ok r er

abbrev prefixText (s t : State) (x : List Byte) := x++bytesAt t.mem (s.gpr .r27) (datPrefix s)
abbrev sourceTail (s : State) := s.gpr .r19+BitVec.ofNat 64 (datPrefix s)
abbrev roundsOf (s : State) := (s.gpr .r28).toNat

private theorem prefixContext {s : State} (p : CoreIn s) :
    ∀ r ∈ prefixAreas s (datPrefix s),(ctxRegion s).Disjoint r :=
  behind p.layout.cs p.slabCtx (p.bounds.dst.ctx.sub_right (Region.sub_prefix (prefixLe _)))

theorem afterPrefix_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s u : State} {icb H : Block} {x : List Byte}
    (p : CoreIn s) (q : PrefixResult s u) (m : PrefixMath s u H icb x)
    (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14) (xa : x.length%16=0) (hash : ctxH s.mem (s.gpr .r29)=H) :
    WP isa VG.Impl.AesGcm.PPC64LE.Contiguous.remaining u
      (RestResult u.gpr s.sp (sourceTail s) (restR s).len (roundsOf s) (datPrefix s) icb H (prefixText s u x) u) := by
  have c := q.saved .r29 (by decide)
  have st := q.saved .r30 (by decide)
  have w := q.saved .r31 (by decide)
  have r := q.saved .r28 (by decide)
  have align : datPrefix s%16=0 := by rw [show datPrefix s=16*prefixBlocks (datLen s) from (prefixEq _).symm];simp
  have suffix := p.bounds.drop (prefixLe _) q.rd q.wr
  refine remaining_wp (V := u.gpr) ⟨fun _ _ => rfl,q.sp,?_⟩ (p.layout.v c st w) q.src q.len ?_ R ?_ align ?_ ?_ ?_ ?_
  · rw [c,st,w];exact p.perm.of_eq q.rd q.wr
  · obtain ⟨a,b,e⟩ := suffix
    refine ⟨?_,?_,?_⟩
    · rw [st,w];exact a
    · rw [c,st,w,q.dst];exact b
    · rw [q.dst];exact e
  · simp [r,roundsOf]
  · simp [prefixText,List.length_append,bytesAt,Nat.add_mod,xa,align]
  · rw [c];exact (ctxH_keep m.frame (prefixContext p)).trans hash
  · rw [st];exact m.auth
  · rw [st,c,ciph_frame m.frame (prefixContext p) R];exact m.ctr

theorem joinRest {s u t : State} {icb H : Block} {x : List Byte}
    (p : CoreIn s) (q : PrefixResult s u) (m : PrefixMath s u H icb x)
    (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14)
    (z : RestResult u.gpr s.sp (sourceTail s) (restR s).len (roundsOf s) (datPrefix s) icb H (prefixText s u x) u t) :
    Joined s t H icb x := by
  have c := q.saved .r29 (by decide)
  have st := q.saved .r30 (by decide)
  have w := q.saved .r31 (by decide)
  have pre := prefixAfter p q z.frame
  have sum : datPrefix s+(restR s).len=datLen s := Nat.add_sub_of_le (prefixLe _)
  have tail := z.cipher
  rw [q.dst,c,ciph_frame m.frame (prefixContext p) R] at tail
  change _=xorKs _ icb (datPrefix s) (bytesAt u.mem (s.gpr .r19+BitVec.ofNat 64 (datPrefix s)) _) at tail
  rw [srcAfter p m.frame] at tail
  have fr := z.frame
  rw [st,w,q.dst] at fr
  refine ⟨z.env.sp,?_,?_,?_,(m.frame.mono fun _ e => List.mem_append_left _ e).trans (fr.mono fun _ e => List.mem_append_right _ e)⟩
  · intro r hr
    have h : r∈frozen ∧ r∈prefixKeep ∧ r≠.r21 ∧ r≠.r19 := by revert r;decide
    rw [z.env.fr r h.1]
    simpa [suffixEnd,cursors,suffixValues,h.2.2.1,h.2.2.2] using q.saved r h.2.1
  · have join := done_appendTo (j := datPrefix s) (l := (restR s).len) (pre.trans m.data) (by rw [Nat.zero_add]; exact tail)
    simpa only [sum] using join
  · have full : bytesAt t.mem (s.gpr .r27) (datLen s)=bytesAt u.mem (s.gpr .r27) (datPrefix s)++
        bytesAt t.mem (u.gpr .r18) (restR s).len := by
      rw [←sum,bytesAt_add,pre,q.dst]
    have h := z.absorbed
    rw [st] at h
    change Auth _ H (paddedTail (prefixText s u x) _) t at h
    rw [full];simpa only [paddedTail,prefixText,List.append_assoc] using h

theorem cipher_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} {icb H : Block} {x : List Byte} (p : CoreIn s)
    (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14)
    (cipher : Ctr s.mem (s.gpr .r30+48) (s.gpr .r30+64) (ctxCiph s.mem (s.gpr .r29) (roundsOf s)) icb 0)
    (auth : Auth (s.gpr .r30) H x s) (xa : x.length%16=0) (hash : ctxH s.mem (s.gpr .r29)=H) :
    WP isa (.seq prefixCode (.ite (.zero .d .r25) (.block []) VG.Impl.AesGcm.PPC64LE.Contiguous.remaining)) s (fun t => Joined s t H icb x) := by
  apply WP.seq
  refine WP.mono (prefix_wp p.access p.read p.write) fun u q => ?_
  have m := q.math cipher auth xa hash
  have fit := Nat.lt_of_le_of_lt (Nat.sub_le (datLen s) (datPrefix s)) p.bounds.src.lt
  refine WP.ite (decide ((restR s).len=0)) (eval_zero q.len fit) (fun yes => ?_) (fun _ => ?_)
  · have zero : (restR s).len=0 := by simpa using yes
    have same : datPrefix s=datLen s := by have h := Nat.add_sub_of_le (prefixLe (datLen s));change datLen s-datPrefix s=0 at zero;change datPrefix s+(datLen s-datPrefix s)=datLen s at h;omega
    have align : datLen s%16=0 := by rw [←same,datPrefix,(prefixEq _).symm];simp
    refine WP.block_nil ⟨q.sp,fun r hr => q.saved r (by revert r;decide),?_,?_,m.frame.mono fun _ e => List.mem_append_left _ e⟩
    · have h := m.data
      change bytesAt u.mem _ (datPrefix s)=xorKs _ _ _ (bytesAt _ _ (datPrefix s)) at h
      rwa [same] at h
    · have h := m.auth
      change Auth (s.gpr .r30) H (x++bytesAt u.mem _ (datPrefix s)) u at h
      rw [same] at h
      simpa [paddedTail,padLen,bytesAt,zeros,Nat.add_mod,xa,align] using h
  · exact WP.mono (afterPrefix_wp p q m R xa hash) fun t => joinRest p q m R

end VG.Proof.AesGcm.PPC64LE.Contiguous
