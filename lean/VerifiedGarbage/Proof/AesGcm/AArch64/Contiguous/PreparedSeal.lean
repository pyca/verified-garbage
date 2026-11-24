module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Batches
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Finish
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagReturn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Compose

/-! The prepared prefix is empty or consists of completed eight-block
groups. Its postcondition records which part of the original source remains. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Spec.Gcm (Block blockAt blocks ghash ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Proof.Gcm.AArch64.Stitch (BatchMid Gh8Ok)
open VG.Proof.AesGcm.AArch64.Stitch (pre tblR)

abbrev prefixFrame (St W O : Addr) (p : Nat) : List Region :=
  [⟨word St 16,16⟩,⟨word St 48,16⟩,⟨O,p⟩,tblR W]

structure Prefix (wn R n p : Nat) (Ctx St W SP D O : Addr) (x : List Byte) (iv : Block) (s t : State) : Prop where
  env : Env wn Ctx St W SP t
  x22 : t.gpr .x22 = s.gpr .x22
  x23 : t.gpr .x23 = D
  x26 : t.gpr .x26 = BitVec.ofNat 64 n
  x28 : t.gpr .x28 = s.gpr .x28
  bytes : bytesAt t.mem O p = xorKs (ciphOf s.mem Ctx R) iv 0 (bytesAt s.mem D p)
  ctr : Ctr t.mem (St+48) (St+64) (ciphOf s.mem Ctx R) iv p
  auth : blockAt t.mem (word St 16) = ghash (ctxH s.mem Ctx) (blocks (x ++ bytesAt t.mem O p))
  frame : Frame (prefixFrame St W O p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem prefix_ok {wn R n : Nat} {Ctx St W SP D O P : Addr} {s : State} {iv : Block} {x : List Byte}
    (fused forward : Bool) (L : Lay wn Ctx St W) (e : Env wn Ctx St W SP s) (gh : Gh8Ok)
    (r : R = 10 ∨ R = 12 ∨ R = 14) (x22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (x23 : s.gpr .x23 = D) (x26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (sd : DataOk wn St W s D n) (od : DataW wn Ctx St W s O n) (mode : BufferLayout D O n)
    (hn : fused = true → 128 ≤ n) (p : GhWCall s Ctx (word St 16) (word W 512) P)
    (pw : s.mem.readW (word s.sp 16) 64 = P) (rp : InRegions (s.rd++s.wr) (word s.sp 16) 8)
    (src : s.mem.readW (word W dataO) 64 = D) (dst : s.mem.readW (word W dstO) 64 = O)
    (cb : blockAt s.mem (word St 48) = iv) (y : blockAt s.mem (word St 16) = ghash (ctxH s.mem Ctx) (blocks x))
    (xm : x.length % 16 = 0) :
    WP isa (if fused then batches forward else .block []) s (Prefix wn R n (done fused n) Ctx St W SP D O x iv s) := by
  cases fused
  · refine WP.block_nil ⟨e,rfl,x23,x26,rfl,rfl,Proof.Gcm.ctr_zero _ _ _ _ cb,?_,Frame.refl _ _,rfl,rfl⟩
    simpa [done,bytesAt] using y
  · refine (batches_ok forward L e gh r x22 x23 x26 sd od mode (hn rfl) p pw rp src dst).mono ?_
    intro t ⟨z,h,reg,td,tn⟩
    have hd := h.data
    have hc := h.ctr
    change Spec.Gcm.blocksAt z.mem O _ = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (word St 48)) _ at hd
    change blockAt z.mem (word St 48) = Nat.repeat _ _ (blockAt s.mem (word St 48)) at hc
    obtain ⟨bytes,ctr⟩ := Proof.Gcm.ctr_wholeTo (ks := St+64) (ciph := ciphOf s.mem Ctx R) (icb := iv)
      (Proof.Gcm.ctr_zero _ _ _ _ cb) (by decide) hd hc
    have eq : 16*(8*(n/128)) = pre n := by unfold pre; omega
    rw [eq] at bytes ctr
    rw [Nat.zero_add] at ctr
    have gr (i : Reg) (hi : i ∈ [Reg.x19,.x20,.x21,.x22,.x28]) : t.gpr i = s.gpr i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact (reg.others _ (by decide)).trans (h.gpr _ (by decide) (by decide) (by decide))
    have rd := reg.rd.trans h.rd
    have wr := reg.wr.trans h.wr
    have en := e.keep (fun i hi => gr i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl|rfl <;> decide))
      (reg.sp.trans h.sp) rd wr
    refine ⟨en,gr _ (by decide),td,tn,gr _ (by decide),reg.mem ▸ bytes,reg.mem ▸ ctr,?_,reg.mem ▸ h.frame,rd,wr⟩
    have hz := h.y
    change blockAt z.mem (word St 16) = Spec.Gcm.ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (word St 16)) _ at hz
    rw [reg.mem,hz,y,Proof.Gcm.blocksAt_eq,eq,Spec.Gcm.ghash,Spec.Gcm.ghash,Proof.Gcm.blocks_append xm,Proof.Gcm.ghashFrom_append]
    rfl

theorem prefixApart {St W O : Addr} {p wn : Nat} {r : Region} (hs : r.Disjoint ⟨St,80⟩)
    (hw : r.Disjoint (workR wn W)) (ho : r.Disjoint ⟨O,p⟩) (lim : 768 ≤ wn) :
    ∀ w ∈ prefixFrame St W O p, r.Disjoint w := by
  intro w hm
  simp only [prefixFrame,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl
  · exact hs.sub_right (Lay.stSub (by decide))
  · exact hs.sub_right (Lay.stSub (by decide))
  · exact ho
  · exact hw.sub_right (Lay.wSub (by omega))

theorem prefix_join {wn R n p : Nat} {Ctx St W SP D O : Addr} {x : List Byte} {iv : Block}
    {s u t : State} {k : Reg → Addr} (L : Lay wn Ctx St W)
    (r : R = 10 ∨ R = 12 ∨ R = 14) (sd : DataOk wn St W s D n) (od : DataW wn Ctx St W s O n)
    (mode : BufferLayout D O n) (hp : p ≤ n) (h : Prefix wn R n p Ctx St W SP D O x iv s u)
    (tail : DirectGather.Generic.Encrypted wn Ctx St W SP k R iv p (word D p) (word O p) (n-p) u.mem t) :
    bytesAt t.mem O n = xorKs (ciphOf s.mem Ctx R) iv 0 (bytesAt s.mem D n) ∧
      blockAt t.mem (word St 16) = ghash (ctxH s.mem Ctx) (blocks (x ++ bytesAt t.mem O p)) := by
  have lim := L.hWn
  have cp := od.take hp
  have split := split_disj (D := O) hp sd.lt
  have apart (v : Region) (hs : v.Disjoint ⟨St,80⟩) (hw : v.Disjoint (workR wn W))
      (ho : v.Disjoint ⟨word O p,n-p⟩) : ∀ w ∈ crFrame wn St W (word O p) (n-p), v.Disjoint w := by
    intro w hm; simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl
    · exact ho
    · exact hs.sub_right (Lay.stSub (by decide))
    · exact hw.sub_right (Lay.wSub (by omega))
  have kept := bytesAt_frame tail.frame (apart _ cp.ok.st cp.ok.w split) (by have := sd.lt; omega)
  have data := sd.drop hp
  have dis : (⟨word D p,n-p⟩ : Region).Disjoint ⟨O,p⟩ := by
    rcases mode with same|dis
    · rw [← same]; exact split.symm
    · exact (dis.sub_left (Offset.sub_base D (by omega))).sub_right (Region.sub_prefix hp)
  have source := bytesAt_frame h.frame (prefixApart data.st data.w dis lim.1) (by have := sd.lt; omega)
  have cipher := ciph_frame h.frame (prefixApart L.cs L.cw' cp.ctx lim.1) r
  have rem := tail.out
  rw [source,cipher] at rem
  have ct := done_append (j := p) (l := n-p) (kept.trans h.bytes) (by simpa only [Nat.zero_add] using rem)
  refine ⟨by simpa only [Nat.add_sub_cancel' hp] using ct,?_⟩
  rw [kept,← h.auth]
  exact blockAt_frame tail.frame fun w hm => by
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl
    · exact ((od.drop hp).ok.st.sub_right (Lay.stSub (by decide))).symm
    · exact Offset.disjoint St (.inl (by decide)) (by decide) (by decide)
    · exact L.st_wn (by decide) (.inr ⟨by decide,by omega⟩)

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## The prepared CTR and GHASH loops may write only these three ranges.
In particular they preserve the caller's tag/length slots, J₀, the cached
hash key, the powers argument and the saved registers. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Gcm (blockAt ctxH)
open VG.Spec.Aes (bytesAt)

abbrev writes (wn : Nat) (St W O : Addr) (n : Nat) : List Region :=
  [⟨word St 16,64⟩,⟨word W 512,wn-512⟩,⟨O,n⟩]

section
variable {wn n p : Nat} {Ctx St W O : Addr} (L : Lay wn Ctx St W) {s : State}
variable {m m' : Mem}

theorem prefix_writes (hp : p ≤ n) (lim : 768 ≤ wn) (f : Frame (prefixFrame St W O p) m m') :
    Frame (writes wn St W O n) m m' := f.sub fun r hr => by
  simp only [prefixFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
  · exact ⟨_,List.mem_cons_self ..,Offset.sub St (by decide) (by decide)⟩
  · exact ⟨_,by simp [writes],Region.sub_prefix hp⟩
  · exact ⟨⟨word W 512,wn-512⟩,by simp [writes],Region.sub_prefix (by omega)⟩

theorem remainder_writes (hp : p ≤ n) (f : Frame (crFrame wn St W (word O p) (n-p)) m m') :
    Frame (writes wn St W O n) m m' := f.sub fun r hr => by
  simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨⟨O,n⟩,by simp [writes],Offset.sub_base O (by omega)⟩
  · exact ⟨_,List.mem_cons_self ..,Offset.sub St (by decide) (by decide)⟩
  · exact ⟨_,by simp [writes],fun _ hr => hr⟩

theorem auth_writes (lim : 768 ≤ wn) (f : Frame (absFrame St W 16) m m') :
    Frame (writes wn St W O n) m m' := f.sub fun r hr => by
  simp only [absFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
  · exact ⟨_,List.mem_cons_self ..,Offset.sub St (by decide) (by decide)⟩
  · exact ⟨⟨word W 512,wn-512⟩,by simp [writes],Region.sub_prefix (by omega)⟩

theorem writes_apart {r : Region} (a : r.Disjoint ⟨word St 16,64⟩) (b : r.Disjoint ⟨word W 512,wn-512⟩)
    (c : r.Disjoint ⟨O,n⟩) : ∀ w ∈ writes wn St W O n, r.Disjoint w := by
  intro w hw; simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw.elim (fun h => h ▸ a) (fun h => h.elim (fun e => e ▸ b) (fun e => e ▸ c))

include L in
theorem writes_ctx (d : DataW wn Ctx St W s O n) : ∀ w ∈ writes wn St W O n, (⟨Ctx,256⟩ : Region).Disjoint w :=
  writes_apart (L.cs.sub_right (Lay.stSub (by decide))) (L.cw'.sub_right (Lay.wSub (by have := L.hWn; omega))) d.ctx

include L in
theorem writes_slot {a k : Nat} (ha : 96 ≤ a) (hi : a+k ≤ 512) (d : DataOk wn St W s O n) :
    ∀ w ∈ writes wn St W O n, (⟨word W a,k⟩ : Region).Disjoint w := by
  have lim := L.hWn
  exact writes_apart (L.st_w (by decide) (.inr ⟨ha,hi⟩)).symm
    (Offset.disjoint W (.inl hi) (by omega) (by omega)) (d.w.symm.sub_left (Lay.wSub (by omega)))

include L in
theorem writes_j0 (d : DataOk wn St W s O n) :
    ∀ w ∈ writes wn St W O n, (⟨St,16⟩ : Region).Disjoint w := by
  have lim := L.hWn
  exact writes_apart (st0_disj L (by decide) (by decide)) (st0_w L ⟨by decide,by omega⟩)
    (d.st.symm.sub_left (Region.sub_prefix (by decide)))

theorem writes_external {r : Region} (sw : St = word W 16) (rw : r.Disjoint (workR wn W))
    (ro : r.Disjoint ⟨O,n⟩) (lim : 768 ≤ wn) : ∀ w ∈ writes wn St W O n, r.Disjoint w := by
  subst St
  exact writes_apart (rw.sub_right (by unfold word; rw [add_ofNat_assoc]; exact Lay.wSub (by omega)))
    (rw.sub_right (Lay.wSub (by omega))) ro

end
end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## Complete payload encryption of the prepared hardware entries, retaining
the GHASH state over the prefix and exactly which original bytes were read. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Spec.Gcm (Block blockAt blocks ghash ctxH j0 inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The AES-GCM record after AAD processing. -/
structure Ready (wn R n : Nat) (Ctx W D O P : Addr) (aad nonce : List Byte) (s : State) : Prop where
  env : Env wn Ctx (word W 16) W s.sp s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x23 : s.gpr .x23 = D
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  rates : R = 10 ∨ R = 12 ∨ R = 14
  src : DataOk wn (word W 16) W s D n
  dst : DataW wn Ctx (word W 16) W s O n
  mode : BufferLayout D O n
  powers : GhWCall s Ctx (word (word W 16) 16) (word W 512) P
  pw : s.mem.readW (word s.sp 16) 64 = P
  pRead : InRegions (s.rd++s.wr) (word s.sp 16) 8
  sourceSlot : s.mem.readW (word W dataO) 64 = D
  dstSlot : s.mem.readW (word W dstO) 64 = O
  lenSlot : s.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n
  aadSlot : s.mem.readW (word W alenO) 64 = BitVec.ofNat 64 aad.length
  j : blockAt s.mem (word W 16) = j0 (ctxH s.mem Ctx) nonce
  cb : blockAt s.mem (word (word W 16) 48) = inc32 (j0 (ctxH s.mem Ctx) nonce)
  y : blockAt s.mem (word (word W 16) 16) = ghash (ctxH s.mem Ctx) (blocks (paddedAad aad))
  key : Fast.KeyAt (ctxH s.mem Ctx) s.mem W

abbrev encPart (c : Callees) (fused forward : Bool) : Prog isa :=
  .seq (if fused then batches forward else .block []) (.seq (.block (remainder fused)) (DirectGather.aligned c))

structure Text (wn R n p : Nat) (Ctx W D O : Addr) (aad nonce : List Byte) (s t : State) : Prop where
  env : Env wn Ctx (word W 16) W s.sp t
  x22 : t.gpr .x22 = s.gpr .x22
  x27 : t.gpr .x27 = word O p
  x28 : t.gpr .x28 = s.gpr .x28
  out : bytesAt t.mem O n = xorKs (ciphOf s.mem Ctx R) (inc32 (j0 (ctxH s.mem Ctx) nonce)) 0 (bytesAt s.mem D n)
  y : blockAt t.mem (word (word W 16) 16) = ghash (ctxH s.mem Ctx) (blocks (paddedAad aad ++ bytesAt t.mem O p))
  frame : Frame (writes wn (word W 16) W O n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem encPart_ok {wn R n : Nat} {Ctx W D O P : Addr} {s : State} {aad nonce : List Byte}
    (v : GcmImpl) (fused : Bool) (gh : Gh8Ok) (L : Lay wn Ctx (word W 16) W)
    (q : Ready wn R n Ctx W D O P aad nonce s) (hn : fused = true → 128 ≤ n) (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (encPart v.callees fused (!v.stitch)) s (Text wn R n (done fused n) Ctx W D O aad nonce s) := by
  have hp := done_le fused n
  have lim := L.hWn
  have align : (paddedAad aad).length % 16 = 0 := by
    simpa only [paddedAad,List.length_append,Proof.Gcm.length_zeros] using Proof.Gcm.length_pad_mod aad.length
  refine WP.seq ((prefix_ok fused (!v.stitch) L q.env gh q.rates q.x22 q.x23 q.x26 q.src q.dst q.mode hn q.powers
    q.pw q.pRead q.sourceSlot q.dstSlot q.cb q.y align).mono ?_)
  intro u h
  have fu := prefix_writes hp lim.1 h.frame
  have cp := ciph_frame fu (writes_ctx L q.dst) q.rates
  have val : u.mem.readW (word W dstO) 64 = O := (fu.readW (r := slotR W dstO) (Region.contains_self _ _)
    (writes_slot L (by decide) (by decide) q.dst.ok) (by decide)).trans q.dstSlot
  have r22 := h.x22.trans q.x22
  have rr : rounds (u.gpr .x22) := by
    rw [r22]; rcases q.rates with e|e|e <;> rw [e] <;> decide
  have nr : (u.gpr .x22).toNat = R := by
    rw [r22,toNat_ofNat_of_lt (by rcases q.rates with e|e|e <;> rw [e] <;> decide)]
  have ctr : Proof.Gcm.Ctr u.mem (word (word W 16) 48) (word (word W 16) 64) (ciphOf u.mem Ctx R)
      (inc32 (j0 (ctxH s.mem Ctx) nonce)) (done fused n) := by rw [cp]; exact h.ctr
  refine (encrypt_remainder v fused L h.env h.x23 h.x26 rr nr (q.src.of_eq h.rd h.wr) (q.dst.of_eq h.rd h.wr)
    q.mode val ctr hv).mono ?_
  intro t ⟨r,targs,body,rd,wr⟩
  have z := prefix_join L q.rates q.src q.dst q.mode hp h body
  exact ⟨body.env,(body.kept _ (by decide)).trans ((targs.others _ (by decide)).trans h.x22),
    (body.kept _ (by decide)).trans targs.start,
    (body.kept _ (by decide)).trans ((targs.others _ (by decide)).trans h.x28),z.1,z.2,
    fu.trans (remainder_writes hp body.frame),rd.trans h.rd,wr.trans h.wr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## The cached powers continue GHASH over exactly the ciphertext written
by the prepared payload body, including its unstitched whole blocks. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Spec.Gcm (Block blockAt blocks ghash ctxH j0 inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)

structure External (wn n : Nat) (W O P : Addr) (s : State) : Prop where
  powersWork : (⟨P,128⟩ : Region).Disjoint (workR wn W)
  powersOut : (⟨P,128⟩ : Region).Disjoint ⟨O,n⟩
  slotWork : (slotR s.sp 16).Disjoint (workR wn W)
  slotOut : (slotR s.sp 16).Disjoint ⟨O,n⟩

structure Auth (wn R n j : Nat) (Ctx W D O : Addr) (aad nonce : List Byte) (s t : State) : Prop where
  env : Env wn Ctx (word W 16) W s.sp t
  x22 : t.gpr .x22 = s.gpr .x22
  x23 : t.gpr .x23 = word O j
  x24 : t.gpr .x24 = BitVec.ofNat 64 (n-j)
  x26 : t.gpr .x26 = BitVec.ofNat 64 n
  x28 : t.gpr .x28 = s.gpr .x28
  bound : j ≤ n
  last : n-j < 16
  out : bytesAt t.mem O n = xorKs (ciphOf s.mem Ctx R) (inc32 (j0 (ctxH s.mem Ctx) nonce)) 0 (bytesAt s.mem D n)
  hash : Fast.padStep (ctxH s.mem Ctx) (blockAt t.mem (word (word W 16) 16)) (bytesAt t.mem (word O j) (n-j)) =
    ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded aad (bytesAt t.mem O n)))
  frame : Frame (writes wn (word W 16) W O n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Text.authInput {wn R n : Nat} {Ctx W D O P : Addr} {s t : State} {aad nonce : List Byte}
    (fused : Bool) (L : Lay wn Ctx (word W 16) W)
    (q : Ready wn R n Ctx W D O P aad nonce s) (ext : External wn n W O P s)
    (txt : Text wn R n (done fused n) Ctx W D O aad nonce s t) :
    t.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n ∧ blockAt t.mem (word Ctx 240) = ctxH s.mem Ctx ∧
    (paddedAad aad ++ bytesAt t.mem O (done fused n)).length%16=0 ∧
    GhWCall t Ctx (word (word W 16) 16) (word W 512) P ∧ t.mem.readW (word t.sp 16) 64 = P ∧
    InRegions (t.rd++t.wr) (word t.sp 16) 8 := by
  have hp := done_le fused n
  have lim := L.hWn
  have sep := writes_external (St := word W 16) rfl ext.slotWork ext.slotOut lim.1
  have ps : t.mem.readW (word t.sp 16) 64 = P := by
    rw [txt.env.sp]; exact (txt.frame.readW (r := slotR s.sp 16) (Region.contains_self _ _) sep (by decide)).trans q.pw
  have hH : blockAt t.mem (word Ctx 240) = ctxH s.mem Ctx := blockAt_frame txt.frame
    (fun w hw => (writes_ctx L q.dst w hw).sub_left (Lay.ctxSub (by decide)))
  have call : GhWCall t Ctx (word (word W 16) 16) (word W 512) P := by
    refine ⟨by rw [txt.rd,txt.wr]; exact q.powers.reads,q.powers.yp,q.powers.sp,?_⟩
    rw [hH]; exact Proof.AesGcm.powers8Repr_congr (fun i hi => txt.frame.bytes (R := ⟨P,128⟩)
      (writes_external rfl ext.powersWork ext.powersOut lim.1) (show 128 ≤ 2^64 by decide) hi) q.powers.repr
  have len := (txt.frame.readW (r := slotR W lenO) (Region.contains_self _ _) (writes_slot L (by decide) (by decide) q.dst.ok)
    (by decide)).trans q.lenSlot
  have xm := done_mod fused n
  have align : (paddedAad aad ++ bytesAt t.mem O (done fused n)).length % 16 = 0 := by
    simp only [paddedAad,List.length_append,Proof.Gcm.length_zeros,length_bytesAt]
    have := Proof.Gcm.length_pad_mod aad.length; omega
  exact ⟨len,hH,align,call,ps,by rw [txt.env.sp,txt.rd,txt.wr]; exact q.pRead⟩

theorem authenticate_ok {wn R n : Nat} {Ctx W D O P : Addr} {s t : State} {aad nonce : List Byte}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (L : Lay wn Ctx (word W 16) W)
    (q : Ready wn R n Ctx W D O P aad nonce s) (ext : External wn n W O P s)
    (txt : Text wn R n (done fused n) Ctx W D O aad nonce s t) :
    let p := done fused n
    WP isa (.seq (.block (authRemainder fused)) (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn)) t
      (Auth wn R n (p+16*((n-p)/16)) Ctx W D O aad nonce s) := by
  have hp := done_le fused n
  have lim := L.hWn
  have xm := done_mod fused n
  obtain ⟨len,hH,align,call,ps,pr⟩ := txt.authInput fused L q ext
  let j := 16*((n-done fused n)/16)
  refine (authCall v g fused L txt.env (q.dst.ok.of_eq txt.rd txt.wr) txt.x27 len hH align call ps pr).mono ?_
  intro u ⟨a,ra,a26,ha,hlt,rd,wr⟩
  have od := q.dst.ok.of_eq (rd.trans txt.rd) (wr.trans txt.wr)
  have hj : j ≤ n-done fused n := ha.le
  have out : bytesAt u.mem O n = bytesAt t.mem O n :=
    bytesAt_frame ha.frame (data_absFrame L (.inr rfl) od) (Nat.le_of_lt od.lt)
  have math := suffixHash L od hp xm (show j%16 = 0 by unfold j; omega) hlt txt.y ha
  have off : word (word O (done fused n)) j = word O (done fused n+j) := by
    unfold word; rw [Offset.add_add]
  have lenEq : n-done fused n-j = n-(done fused n+j) := by omega
  refine ⟨ha.env,(ha.kept _ (by decide)).trans ((ra.others _ (by decide)).trans txt.x22),ha.x23.trans off,
    ha.x24.trans (congrArg _ lenEq),(ha.kept _ (by decide)).trans a26,
    (ha.kept _ (by decide)).trans ((ra.others _ (by decide)).trans txt.x28),by omega,by omega,
    out.trans txt.out,?_,txt.frame.trans (auth_writes lim.1 ha.frame),rd.trans txt.rd,wr.trans txt.wr⟩
  rw [out]; exact math

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## A prepared record after the AAD is absorbed: authenticate, encrypt the
tag, restore registers and return both outputs against the original source. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Spec.Gcm (Block blockAt ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

abbrev finalPart : Prog isa :=
  .seq finishProgram (.seq (Impl.Gcm.AArch64.Stitch.byRounds Impl.AesGcm.AArch64.Contiguous.Tag.finish) (.block restore))

abbrev recordWrites (wn : Nat) (W O Tg : Addr) (n : Nat) : List Region := [workR wn W,⟨O,n⟩,⟨Tg,16⟩]

theorem ws_work {wn : Nat} {W : Addr} (lim : 768 ≤ wn) : ∀ r ∈ Fast.wsR wn W, Region.Sub r (workR wn W) := by
  intro r hr; simp only [Fast.wsR,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Region.sub_prefix (by omega)
  · exact Lay.wSub (by change 288+32≤wn; omega)
  · exact Lay.wSub (by omega)

theorem finalPart_ok {wn R n j : Nat} {Ctx W D O P Tg : Addr} {s t o : State} {aad nonce : List Byte}
    (mk : MulKey) (L : Lay wn Ctx (word W 16) W)
    (q : Ready wn R n Ctx W D O P aad nonce s) (h : Auth wn R n j Ctx W D O aad nonce s t)
    (ha : aad.length < 2^64) (sv : SavedAt s.mem W o) (sp : s.sp = o.sp)
    (tag : Covers [⟨Tg,16⟩] s.wr) (x28 : s.gpr .x28 = Tg)
    (tw : (⟨Tg,16⟩ : Region).Disjoint (workR wn W)) (ot : (⟨O,n⟩ : Region).Disjoint ⟨Tg,16⟩) :
    WP isa finalPart t fun z => GprAbi o z ∧ Frame (recordWrites wn W O Tg n) s.mem z.mem ∧
      Spec.Gcm.encryptWith (ciphOf s.mem Ctx R) (ctxH s.mem Ctx) 16 nonce (bytesAt s.mem D n) aad =
        (bytesAt z.mem O n,bytesAt z.mem Tg 16) := by
  have lim := L.hWn
  have key := q.key.frame h.frame (writes_slot L (by decide) (by decide) q.dst.ok)
  have al := (h.frame.readW (r := slotR W alenO) (Region.contains_self _ _) (writes_slot L (by decide) (by decide) q.dst.ok)
    (by decide)).trans q.aadSlot
  have saved := sv.frame h.frame (writes_slot L (by decide) (by decide) q.dst.ok)
  have j0 := (blockAt_frame h.frame (writes_j0 L q.dst.ok)).trans q.j
  have ct := h.out
  rw [← Proof.Gcm.gctr_eq] at ct
  refine WP.seq ((WP.with_rdwr (finish_ok mk h.env (q.dst.ok.of_eq h.rd h.wr) key h.bound h.last
    h.x23 h.x24 h.x26)).mono ?_)
  intro u ⟨⟨y,uk,ue,u22,u26,u28,fu⟩,_,wr⟩
  have fm : Frame (Fast.wsR wn W) t.mem u.mem := fu.sub fun r hr => by
    have eq := List.mem_singleton.mp hr; subst r; exact Fast.sub_low (by decide)
  have ual := (fu.readW (r := slotR W alenO) (Region.contains_self _ _) (by
    intro r hr; have eq := List.mem_singleton.mp hr; subst r
    exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)) (by decide)).trans al
  have uj : blockAt u.mem (word W 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) nonce :=
    (blockAt_frame fu (fun r hr => by have eq := List.mem_singleton.mp hr; subst r
                                      exact st0_w L ⟨by decide,by omega⟩)).trans j0
  rw [h.hash] at y
  refine (Tag.return_ok mk (sp ▸ ue) uk y q.rates (u22.trans (h.x22.trans q.x22)) u26 q.src.lt ual ha
    (saved.frame fm (Fast.saved_wsR lim)) (by rw [wr,h.wr]; exact tag)
    (u28.trans (h.x28.trans x28)) tw).mono ?_
  intro z ⟨hout,abi,fz⟩
  rw [uj] at hout
  have ow : ∀ r ∈ Fast.wsR wn W, (⟨O,n⟩ : Region).Disjoint r := fun r hr => q.dst.ok.w.sub_right (ws_work lim.1 r hr)
  have cz : ciphOf u.mem Ctx R = ciphOf s.mem Ctx R := (ciph_frame fm (fun r hr => L.cw'.sub_right (ws_work lim.1 r hr))
    q.rates).trans (ciph_frame h.frame (writes_ctx L q.dst) q.rates)
  have oz : bytesAt z.mem O n = bytesAt t.mem O n := (bytesAt_frame fz (fun r hr => by
    have eq := List.mem_singleton.mp hr; subst r; exact ot) (Nat.le_of_lt q.src.lt)).trans
    (bytesAt_frame fm ow (Nat.le_of_lt q.src.lt))
  have fw : Frame (recordWrites wn W O Tg n) s.mem z.mem := by
    refine (h.frame.sub fun r hr => ?_).trans ((fm.sub fun r hr => ⟨_,List.mem_cons_self ..,ws_work lim.1 r hr⟩).trans
      (fz.sub fun r hr => ?_))
    · simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,List.mem_cons_self ..,by unfold word; rw [add_ofNat_assoc]; exact Lay.wSub (by omega)⟩
      · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by omega)⟩
      · exact ⟨_,by simp [recordWrites],fun _ hr => hr⟩
    · have eq := List.mem_singleton.mp hr; subst r; exact ⟨_,by simp,fun _ hr => hr⟩
  refine ⟨abi,fw,?_⟩
  rw [Spec.Gcm.encryptWith,← ct,Proof.Gcm.fullTag_eq,length_bytesAt,oz,hout,cz,List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

abbrev afterFront (c : Callees) (gh : Fn) (fused forward : Bool) : Prog isa :=
  .seq (encPart c fused forward) (.seq (.seq (.block (authRemainder fused)) (Impl.AesGcm.AArch64.Fast.pwSel c 16 gh)) finalPart)

theorem afterFront_ok {wn R n : Nat} {Ctx W D O P Tg : Addr} {s o : State} {aad nonce : List Byte}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (gh : Gh8Ok) (mk : MulKey) (L : Lay wn Ctx (word W 16) W)
    (q : Ready wn R n Ctx W D O P aad nonce s) (ext : External wn n W O P s) (hn : fused = true → 128 ≤ n)
    (ha : aad.length < 2^64) (hv : v.ctr.scratch ≤ wn-512) (sv : SavedAt s.mem W o) (sp : s.sp = o.sp)
    (tag : Covers [⟨Tg,16⟩] s.wr) (x28 : s.gpr .x28 = Tg)
    (tw : (⟨Tg,16⟩ : Region).Disjoint (workR wn W)) (ot : (⟨O,n⟩ : Region).Disjoint ⟨Tg,16⟩) :
    WP isa (afterFront v.callees g.fn fused (!v.stitch)) s fun z => GprAbi o z ∧ Frame (recordWrites wn W O Tg n) s.mem z.mem ∧
      Spec.Gcm.encryptWith (ciphOf s.mem Ctx R) (ctxH s.mem Ctx) 16 nonce (bytesAt s.mem D n) aad =
        (bytesAt z.mem O n,bytesAt z.mem Tg 16) := by
  refine WP.seq ((encPart_ok v fused gh L q hn hv).mono ?_)
  intro t txt
  exact WP.seq ((authenticate_ok v g fused L q ext txt).mono fun u h =>
    finalPart_ok mk L q h ha sv sp tag x28 tw ot)

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
