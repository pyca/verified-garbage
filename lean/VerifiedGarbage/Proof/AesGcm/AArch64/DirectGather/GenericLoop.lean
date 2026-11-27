module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
public import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericStream
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The effect of a gather batch on the descriptor loop's counter and hash
positions, including the pending ciphertext from earlier descriptors. -/
@[expose] public section
namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Stitch (pre sFrame tblR)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64.DirectGather (hashO)

abbrev batchFrame (Wn : Nat) (O St W : Addr) (b : Nat) : List Region :=
  [⟨O, b⟩, ⟨St + BitVec.ofNat 64 16, 16⟩, ⟨St + BitVec.ofNat 64 48, 32⟩,
   ⟨W + BitVec.ofNat 64 hashO, 8⟩, ⟨W + BitVec.ofNat 64 512, Wn - 512⟩]

structure BatchProgress (Wn R n T : Nat) (Ctx St W SP D O B : Addr) (icb Y : Block) (s t : State)
    (b j : Nat) : Prop where
  le : b ≤ n
  whole : 16 ∣ b
  hashed : 16*j ≤ T+b
  data : bytesAt t.mem O b = xorKs (ciphOf s.mem Ctx R) icb T (bytesAt s.mem D b)
  ctr : Ctr t.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb (T+b)
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = ghashFrom (Spec.Gcm.ctxH s.mem Ctx) Y (blocksAt t.mem B j)
  hashPtr : t.mem.readW (W + BitVec.ofNat 64 hashO) 64 = B + BitVec.ofNat 64 (16*j)
  src : t.gpr .x23 = D + BitVec.ofNat 64 b
  dst : t.gpr .x26 = O + BitVec.ofNat 64 b
  rest : t.gpr .x24 = BitVec.ofNat 64 (n-b)
  env : Env Wn Ctx St W SP t
  saved : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ≠ .x26 → r ≠ .x30 → t.gpr r = s.gpr r
  frame : Frame (batchFrame Wn O St W b) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem batches_progress {Wn R n T h k : Nat} {Ctx St W SP D O B : Addr} {icb Y : Block} {s t : State}
    (hs : BatchIn Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W)
    (whole : T = 16 * (h+k)) (atO : O = B + BitVec.ofNat 64 T)
    (base : DataW Wn Ctx St W s B (T+n))
    (hy : blockAt s.mem (St + BitVec.ofNat 64 16) = ghashFrom (Spec.Gcm.ctxH s.mem Ctx) Y (blocksAt s.mem B h))
    (hc : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb T)
    (slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = B + BitVec.ofNat 64 (16*h))
    (res : BatchesPost Ctx St W D O (B + BitVec.ofNat 64 (16*h)) R n k s t) :
    ∃ b j, b = (if batchTest n = 0 then 0 else pre n) ∧
      j = (if batchTest n = 0 then h else (T+b)/16) ∧ BatchProgress Wn R n T Ctx St W SP D O B icb Y s t b j := by
  rcases res with ⟨zero, q⟩ | ⟨nz, u, p, z⟩
  · refine ⟨0, h, by simp [zero], by simp [zero], Nat.zero_le _, ⟨0,rfl⟩, by omega, by rfl, by simpa only [q.mem, Nat.add_zero] using hc,
      by simpa only [q.mem] using hy, by rwa [q.mem], by rw [q.others _ (by decide), hs.x23]; simp,
      by rw [q.others _ (by decide), hs.x26]; simp, by rw [q.others _ (by decide), hs.x24, Nat.sub_zero],
      hs.env.of_regs q, fun r hr _ _ _ _ => q.others r (by simp only [List.mem_singleton]; intro e; subst r; contradiction),
      q.mem ▸ Frame.refl _ _, q.rd, q.wr⟩
  have hw := L.hWn
  have pSep {X : Region} (xs : X.Disjoint ⟨St,80⟩) (xw : X.Disjoint ⟨W,Wn⟩) :
      ∀ r ∈ [⟨St + BitVec.ofNat 64 16,16⟩, ⟨W + BitVec.ofNat 64 512,256⟩], X.Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact xs.sub_right (Lay.stSub (by decide))
    · exact xw.sub_right (Lay.wSub (by omega))
  have keySep := pSep L.cs L.cw'
  have cipher := ciph_frame p.frame keySep hs.rounds
  have hash : Spec.Gcm.ctxH u.mem Ctx = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame p.frame fun r hr => (keySep r hr).sub_left (Lay.ctxSub (by decide))
  have hc' : Ctr u.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb T :=
    Ctr.frame p.frame (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact L.st_st (.inr (by decide)) (by decide) (by decide)
      · exact L.st_wn (by decide) (.inr ⟨by decide, by omega⟩)) hc
  have npre : pre n ≤ n := Nat.mul_div_le n _
  have bsize : 16*(8*(n/128)) = pre n := by unfold pre; omega
  have data := z.data
  rw [cipher] at data
  obtain ⟨bytes, ctr⟩ := Proof.Gcm.ctr_wholeTo hc' (by omega) data z.ctr
  rw [bsize] at bytes ctr
  rw [bytesAt_frame p.frame (fun r hr =>
    (pSep hs.src.st hs.src.w r hr).sub_left (Region.sub_prefix npre)) (by have := hs.src.lt; omega)] at bytes
  have F : Frame (batchFrame Wn O St W (pre n)) s.mem t.mem :=
    (p.frame.sub fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St + BitVec.ofNat 64 16,16⟩, by simp [batchFrame], fun _ hx => hx⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, Wn-512⟩, by simp [batchFrame], Region.sub_prefix (by omega)⟩).trans
    (z.frame.sub fun r hr => by
      simp only [sFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 hashO,8⟩, by simp [batchFrame], fun _ hx => hx⟩
      · exact ⟨⟨St + BitVec.ofNat 64 16,16⟩, by simp [batchFrame], fun _ hx => hx⟩
      · exact ⟨⟨St + BitVec.ofNat 64 48,32⟩, by simp [batchFrame], Region.sub_prefix (by decide)⟩
      · exact ⟨⟨O,pre n⟩, by simp [batchFrame], fun _ hx => hx⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512,Wn-512⟩, by simp [batchFrame], Region.sub_prefix (by omega)⟩)
  have keptPrefix : blocksAt t.mem B (h+k) = blocksAt s.mem B (h+k) := by
    apply blocksAt_frame F
    · intro r hr
      simp only [batchFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      have sub : Region.Sub ⟨B,16*(h+k)⟩ ⟨B,T+n⟩ := Region.sub_prefix (by omega)
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [atO]; exact Offset.base_disjoint _ (by omega) (by have := base.ok.lt; omega)
      · exact (base.ok.st.sub_left sub).sub_right (Lay.stSub (by decide))
      · exact (base.ok.st.sub_left sub).sub_right (Lay.stSub (by decide))
      · exact (base.ok.w.sub_left sub).sub_right (Lay.wSub (by unfold hashO; omega))
      · exact (base.ok.w.sub_left sub).sub_right (Lay.wSub (by omega))
    · have := base.ok.lt; omega
  have jsize : 16*(h+k+8*(n/128)) = T+pre n := by omega
  have rd := z.rd.trans p.rd
  have wr := z.wr.trans p.wr
  have keep (r : Reg) (hr : r ∈ preserved) (h23 : r ≠ .x23) (h24 : r ≠ .x24) (h26 : r ≠ .x26) (h30 : r ≠ .x30) :=
    (z.saved r hr h23 h24 h26 h30).trans (p.saved r hr h30)
  refine ⟨pre n, h+k+8*(n/128),by rw [ite_eq_right nz],by rw [ite_eq_right nz]; omega, npre, ⟨_, bsize.symm⟩, Nat.le_of_eq jsize, bytes, ctr, ?_, ?_, z.src, z.dst,
    by rw [z.rest]; congr 1; unfold pre; omega, hs.env.keep (fun r hr => ?_) (z.sp.trans p.sp) rd wr,
    keep, F, rd, wr⟩
  · rw [z.y, hash, p.out, hy, Proof.Gcm.blocksAt_add t.mem B (h+k), keptPrefix,
      Proof.Gcm.blocksAt_add s.mem B h k, ← whole, ← atO, Proof.Gcm.ghashFrom_append, Proof.Gcm.ghashFrom_append]
    rfl
  · rw [z.hashPtr, atO, Offset.add_add, jsize]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide)

end VG.Proof.Gcm.AArch64.Stitch

/-! Frame rules for growing the ciphertext prefix in the generic gather loop. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)
variable {a : TextArgs} {s t u : State} {n h k : Nat} {pt : List Byte}

theorem textApart {r : Region} {O : Addr} {count : Nat} (pr : PiecesPre a s)
    (dst : r.Disjoint ⟨O,count⟩) (st : r.Disjoint ⟨a.St,80⟩) (w : r.Disjoint ⟨a.W,a.Wn⟩) :
    ∀ q ∈ textFrame a O count, r.Disjoint q := by
  intro q hq; simp only [textFrame,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact dst
  · exact st.sub_right (Lay.stSub (by decide))
  · exact st.sub_right (Lay.stSub (by decide))
  · exact w.sub_right (Lay.wSub (by have := pr.lay.hWn; change 352+8 ≤ a.Wn; omega_arith))
  · exact w.sub_right (Lay.wSub (by have := pr.lay.hWn; omega_arith))

theorem StreamAt.cipher (c : StreamAt a s pt n h t) (pr : PiecesPre a s) (hb : n ≤ a.total s) :
    a.ciph t = a.ciph s :=
  ciph_frame c.frame (textApart pr (pr.dst.ctx.sub_right (Region.sub_prefix hb)) pr.lay.cs pr.lay.cw') pr.rounds

theorem StreamAt.data {D : Addr} {l : Nat} (c : StreamAt a s pt n h t) (pr : PiecesPre a s)
    (hb : n ≤ a.total s) (ok : DataOk a.Wn a.St a.W s D l) (dst : (⟨D,l⟩ : Region).Disjoint ⟨a.dst,a.total s⟩) :
    bytesAt t.mem D l = bytesAt s.mem D l :=
  bytesAt_frame c.frame (textApart pr (dst.sub_right (Region.sub_prefix hb)) ok.st ok.w) (Nat.le_of_lt ok.lt)

theorem frameGrow {m m' : Mem} {base O : Addr} {j l : Nat} {rs rs' : List Region}
    (f : Frame (⟨O,l⟩::rs) m m') (cover : Region.Sub ⟨O,l⟩ ⟨base,j⟩) (other : ∀ r ∈ rs, r ∈ rs') :
    Frame (⟨base,j⟩::rs') m m' := f.sub fun r hr => by
  rcases List.mem_cons.mp hr with rfl|hm
  · exact ⟨_,List.mem_cons_self ..,cover⟩
  · exact ⟨_,List.mem_cons_of_mem _ (other _ hm),fun _ h => h⟩

theorem StreamAt.extend (c : StreamAt a s pt n h t) (pr : PiecesPre a s) (hb : n+k ≤ a.total s)
    (xs : List Byte) (hl : pt.length = n) {h' : Nat}
    (en : Env a.Wn a.Ctx a.St a.W a.SP u) (rounds : u.gpr .x22 = BitVec.ofNat 64 a.R)
    (off : u.gpr .x25 = BitVec.ofNat 64 ((n+k)%16)) (dst : u.gpr .x26 = atOff a.dst (n+k))
    (rd : u.rd = t.rd) (wr : u.wr = t.wr)
    (ctr : Ctr u.mem (a.St+48) (a.St+64) (a.ciph s) a.icb (n+k))
    (out : bytesAt u.mem (atOff a.dst n) k = xorKs (a.ciph s) a.icb n xs)
    (bound : 16*h' ≤ n+k) (hashPtr : u.mem.readW (a.W+352) 64 = atOff a.dst (16*h'))
    (y : blockAt u.mem (a.St+16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem a.Ctx) (blockAt s.mem (a.St+16))
      (blocksAt u.mem a.dst h'))
    (frame : Frame (textFrame a (atOff a.dst n) k) t.mem u.mem) :
    StreamAt a s (pt++xs) (n+k) h' u := by
  have lt := pr.dst.ok.lt
  have head := (pr.dst.take (by omega_arith : n ≤ a.total s)).ok
  have apart : (⟨a.dst,n⟩ : Region).Disjoint ⟨atOff a.dst n,k⟩ := by
    have e := split_disj (D := a.dst) (j := n) (n := n+k) (by omega_arith) (by omega_arith)
    simpa [atOff] using e
  have same := bytesAt_frame frame (textApart pr apart head.st head.w) (by omega_arith)
  refine ⟨en,rounds,off,dst,rd.trans c.rd,wr.trans c.wr,ctr,?_,bound,hashPtr,y,?_⟩
  · rw [bytesAt_add,same,c.out,Proof.Gcm.xorKs_append,hl,Nat.zero_add]; exact congrArg _ out
  · exact (frameGrow c.frame (Region.sub_prefix (Nat.le_add_right n k)) (fun _ x => x)).trans
      (frameGrow frame (Offset.sub_base _ (Nat.le_refl _)) (fun _ x => x))

theorem crSub {O : Addr} {m m' : Mem} {k : Nat} (f : Frame (crFrame a.Wn a.St a.W O k) m m') :
    Frame (textFrame a O k) m m' := f.mono fun r hr => by
  simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> simp [textFrame,atOff]

theorem keepsHash {k : Nat} (c : StreamAt a s pt n h t) (pr : PiecesPre a s)
    (hb : n+k ≤ a.total s) (f : Frame (crFrame a.Wn a.St a.W (atOff a.dst n) k) t.mem u.mem) :
    u.mem.readW (a.W+352) 64 = atOff a.dst (16*h) ∧
    blockAt u.mem (a.St+16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem a.Ctx) (blockAt s.mem (a.St+16))
      (blocksAt u.mem a.dst h) := by
  have lt := pr.dst.ok.lt
  have hn := pr.lay.hWn
  have dsub : Region.Sub ⟨atOff a.dst n,k⟩ ⟨a.dst,a.total s⟩ := Offset.sub_base _ hb
  have wd := (pr.dst.ok.w.sub_left dsub).symm
  have sd := (pr.dst.ok.st.sub_left dsub).symm
  have slot : ∀ r ∈ crFrame a.Wn a.St a.W (atOff a.dst n) k, (⟨a.W+352,8⟩ : Region).Disjoint r := by
    intro r hr; simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact wd.sub_left (Lay.wSub (d := 352) (by omega_arith))
    · exact (pr.lay.sb.sub_left (Lay.stSub (d := 48) (by decide))).symm.sub_left
        (by change Region.Sub ⟨a.W+BitVec.ofNat 64 (96+256),8⟩ _; simpa only [Offset.add_add] using
          Offset.sub_base (a.W+BitVec.ofNat 64 96) (d := 256) (n := 8) (k := a.Wn-96) (by omega_arith))
    · exact Offset.disjoint a.W (.inl (by decide : 352+8 ≤ 512)) (by decide) (by omega_arith)
  have ys : ∀ r ∈ crFrame a.Wn a.St a.W (atOff a.dst n) k, (⟨a.St+16,16⟩ : Region).Disjoint r := by
    intro r hr; simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact sd.sub_left (Lay.stSub (d := 16) (by decide))
    · exact Offset.disjoint a.St (.inl (by decide : 16+16 ≤ 48)) (by decide) (by decide)
    · exact (pr.lay.sb.sub_left (Lay.stSub (d := 16) (by decide))).sub_right
        (by simpa only [Offset.add_add] using
          Offset.sub_base (a.W+BitVec.ofNat 64 96) (d := 416) (n := a.Wn-512) (k := a.Wn-96) (by omega_arith))
  have hbound := c.hashBound
  have hd := (pr.dst.take (by omega_arith : 16*h ≤ a.total s)).ok
  have dj : (⟨a.dst,16*h⟩ : Region).Disjoint ⟨atOff a.dst n,k⟩ := by
    have dj' := Offset.disjoint a.dst (d := 0) (n := 16*h) (e := n) (k := k) (.inl (by omega_arith))
      (by omega_arith) (by omega_arith)
    simpa [atOff] using dj'
  have bs := blocksAt_frame (crSub f) (textApart pr dj hd.st hd.w) (by omega_arith)
  exact ⟨(f.readW (Region.contains_self _ _) slot (by decide)).trans c.hashPtr,
    by rw [blockAt_frame f ys,c.y,bs]⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Stream and descriptor cursors between the three encryption stages of a piece. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Proof.AesGcm.AArch64.Gather (sb sl gl_succ gl_mono)
abbrev frag (a : TextArgs) (s : State) (i : Nat) := sb s.mem a.src i
abbrev len (a : TextArgs) (s : State) (i : Nat) := sl s.mem a.src i
abbrev pos (a : TextArgs) (s : State) (i j : Nat) := a.gl s i + j
abbrev plain (a : TextArgs) (s : State) (i j : Nat) := a.pt s i ++ bytesAt s.mem (frag a s i) j

structure PieceAt (a : TextArgs) (s : State) (i j h : Nat) (t : State) : Prop
    extends StreamAt a s (plain a s i j) (pos a s i j) h t where
  le : j ≤ len a s i
  src : t.gpr .x23 = atOff (frag a s i) j
  rest : t.gpr .x24 = BitVec.ofNat 64 (len a s i-j)
  desc : t.gpr .x27 = atOff a.src (16*(i+1))
  count : t.gpr .x28 = BitVec.ofNat 64 (a.count-i)

variable {a : TextArgs} {s t u : State} {i j h b : Nat}
theorem pieceBound (a : TextArgs) (s : State) {i : Nat} (hi : i < a.count) :
    a.gl s i + len a s i ≤ a.total s := by
  rw [TextArgs.gl,len,← gl_succ]; exact gl_mono _ _ hi

theorem PieceAt.inputs (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count) :
    CrInG a.Wn true a.Ctx a.St a.W a.SP t.gpr a.R (pos a s i j)
      (atOff (frag a s i) j) (atOff a.dst (pos a s i j)) (len a s i-j) t := by
  have lim := pieceBound a s hi
  have bound := p.le
  have ok := (pr.source i hi).drop p.le
  have od := (pr.dst.drop (by dsimp [pos]; omega_arith : pos a s i j ≤ a.total s)).take
    (k := len a s i-j) (by dsimp [pos]; omega_arith)
  have layout : BufferLayout (atOff (frag a s i) j) (atOff a.dst (pos a s i j)) (len a s i-j) := by
    rcases pr.sourceLayout i hi with same | apart
    · left
      simp only [frag,same,pos,atOff,Offset.add_add]
    · right
      exact (apart.sub_left (Offset.sub_base _ (d := j) (n := len a s i-j)
        (by change j+(len a s i-j) ≤ len a s i; omega_arith))).sub_right (Offset.sub_base _ (d := pos a s i j) (by dsimp [pos]; omega_arith))
  exact ⟨p.env,fun _ _ => rfl,p.x22,pr.rounds,p.src,p.rest,p.offset,ok.of_eq p.rd p.wr,
    ⟨od.of_eq p.rd p.wr, layout, by simpa using p.dst⟩⟩

theorem PieceAt.sourceBytes (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count)
    (hstep : j+b ≤ len a s i) :
    bytesAt t.mem (atOff (frag a s i) j) b = bytesAt s.mem (atOff (frag a s i) j) b := by
  have lim := pieceBound a s hi
  have bound := p.le
  have data := ((pr.source i hi).drop bound).take (k := b) (by change b ≤ len a s i-j; omega_arith)
  apply bytesAt_frame p.frame (textApart pr ?_ data.st data.w) (Nat.le_of_lt data.lt)
  rcases pr.sourceLayout i hi with same | apart
  · simp only [same,pos,atOff,Offset.add_add]
    exact Offset.disjoint_base _ (Nat.le_refl _) (by have := pr.dst.ok.lt; omega_arith)
  · exact (apart.sub_left (Offset.sub_base _ hstep)).sub_right (Region.sub_prefix (by dsimp [pos]; omega_arith))

theorem PieceAt.advance (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count)
    {nh : Nat} (hstep : j+b ≤ len a s i)
    (en : Env a.Wn a.Ctx a.St a.W a.SP u) (rounds : u.gpr .x22 = BitVec.ofNat 64 a.R)
    (off : u.gpr .x25 = BitVec.ofNat 64 ((pos a s i j+b)%16))
    (src : u.gpr .x23 = atOff (atOff (frag a s i) j) b)
    (dst : u.gpr .x26 = atOff (atOff a.dst (pos a s i j)) b)
    (rest : u.gpr .x24 = BitVec.ofNat 64 ((len a s i-j)-b))
    (desc : u.gpr .x27 = t.gpr .x27) (count : u.gpr .x28 = t.gpr .x28)
    (rd : u.rd = t.rd) (wr : u.wr = t.wr)
    (ctr : Ctr u.mem (a.St+48) (a.St+64) (a.ciph t) a.icb (pos a s i j+b))
    (out : bytesAt u.mem (atOff a.dst (pos a s i j)) b = xorKs (a.ciph t) a.icb (pos a s i j)
      (bytesAt t.mem (atOff (frag a s i) j) b))
    (hashBound : 16*nh ≤ pos a s i j+b) (hashPtr : u.mem.readW (a.W+352) 64 = atOff a.dst (16*nh))
    (y : blockAt u.mem (a.St+16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem a.Ctx) (blockAt s.mem (a.St+16))
      (blocksAt u.mem a.dst nh))
    (frame : Frame (textFrame a (atOff a.dst (pos a s i j)) b) t.mem u.mem) :
    PieceAt a s i (j+b) nh u := by
  have lim := pieceBound a s hi
  have hb : pos a s i j+b ≤ a.total s := by dsimp [pos]; omega_arith
  have cipher := p.cipher pr (by omega_arith)
  have read := p.sourceBytes pr hi hstep
  rw [cipher] at ctr out
  rw [read] at out
  have hl : (plain a s i j).length = pos a s i j := by
    simp only [plain,pos,List.length_append,VG.Proof.Gcm.length_gathered,length_bytesAt,TextArgs.pt,TextArgs.gl]
  have st := p.extend pr hb _ hl en rounds off (by simpa only [atOff,Offset.add_add] using dst)
    rd wr ctr out hashBound hashPtr y frame
  refine ⟨?_, hstep,by simpa only [atOff,Offset.add_add] using src,by simpa only [Nat.sub_sub] using rest,
    desc.trans p.desc,count.trans p.count⟩
  simpa only [plain,pos,bytesAt_add (m := s.mem) (p := frag a s i) (a := j) (b := b),atOff,Nat.add_assoc,
    List.append_assoc] using st

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Relate each encryption stage to the caller's entire ciphertext prefix. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (aligned batches leftover)
open VG.Proof.Gcm.AArch64.Stitch (batchTest BatchIn PendingIn batches_ok batches_progress)
variable {a : TextArgs} {s t : State} {i j h : Nat}

theorem PieceAt.head_exact (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count) :
    WP isa leftover t fun u => let z := j+crHead (pos a s i j%16) (len a s i-j)
      PieceAt a s i z h u ∧ (len a s i-z = 0 ∨ (pos a s i z)%16=0) := by
  have inc := p.inputs pr hi
  have lim := pieceBound a s hi
  have bound := p.le
  let b := crHead (pos a s i j%16) (len a s i-j)
  have hb : j+b ≤ len a s i := by simp [b,crHead]; split <;> omega_arith
  have cip := p.cipher pr (by dsimp [pos]; omega_arith)
  have ctr : VG.Proof.Gcm.Ctr t.mem (a.St+48) (a.St+64) (a.ciph t) a.icb (pos a s i j) := by rw [cip]; exact p.ctr
  refine (leftover_ok inc ctr).mono fun u q => ?_
  have cf : Frame (crFrame a.Wn a.St a.W (atOff a.dst (pos a s i j)) b) t.mem u.mem :=
    q.frame.mono fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))
  obtain ⟨slot,y⟩ := keepsHash p.toStreamAt pr (by dsimp [pos]; omega_arith) cf
  refine ⟨p.advance pr hi hb q.env q.x22 q.offset q.src q.dst q.rest (q.kept _ (by decide))
    (q.kept _ (by decide)) q.rd q.wr q.ctr q.out (by have := p.hashBound; omega_arith) slot y (crSub cf),?_⟩
  simp only [crHead,pos]
  split <;> omega_arith

theorem PieceAt.tail (v : GcmImpl) (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count)
    (whole : len a s i-j = 0 ∨ pos a s i j%16 = 0) (hv : v.ctr.scratch ≤ a.Wn-512) :
    WP isa (.ite (.zero .x .x24) (.block []) (aligned v.callees)) t (PieceAt a s i (len a s i) h) := by
  have inc := p.inputs pr hi
  have lim := pieceBound a s hi
  have bound := p.le
  have lt := (pr.source i hi).lt
  change len a s i < 2^64 at lt
  refine WP.ite (decide (len a s i-j=0)) (eval_zero p.rest (by omega_arith)) (fun e => ?_) (fun e => ?_)
  · have eqn := of_decide_eq_true e
    have ej : j = len a s i := by omega_arith
    exact WP.block_nil (ej ▸ p)
  have neq := of_decide_eq_false e
  have cip := p.cipher pr (by dsimp [pos]; omega_arith)
  have ctr : VG.Proof.Gcm.Ctr t.mem (a.St+48) (a.St+64) (a.ciph t) a.icb (pos a s i j) := by rw [cip]; exact p.ctr
  obtain ⟨tr,u,ex,q⟩ := aligned_ok pr.lay v inc (whole.resolve_left neq) ctr hv
  refine ⟨tr,u,ex,?_⟩
  obtain ⟨rd,wr,_⟩ := VG.AArch64.Exec.rdwr ex
  have endAt : j+(len a s i-j) = len a s i := Nat.add_sub_of_le bound
  obtain ⟨slot,y⟩ := keepsHash p.toStreamAt pr (by dsimp [pos]; omega_arith) q.frame
  have done := p.advance pr hi (Nat.le_of_eq endAt) q.env ((q.kept _ (by decide)).trans p.x22) q.offset
    q.src q.dst (by rw [Nat.sub_self]; exact q.rest) (q.kept _ (by decide)) (q.kept _ (by decide))
    rd wr q.ctr q.out (by have := p.hashBound; omega_arith) slot y (crSub q.frame)
  exact endAt ▸ done

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Integrate interleaved encryption and GHASH into the descriptor cursor. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (batches)
open VG.Proof.Gcm.AArch64.Stitch (batchTest BatchIn PendingIn batches_ok batches_progress GatherLaws)
variable {a : TextArgs} {s t : State} {i j h : Nat}

theorem StreamAt.ofRegs {u : State} {pt : List Byte} {n : Nat} (p : StreamAt a s pt n h t) {rs : List Reg}
    (r : Regs rs t u) (keep : ∀ z ∈ [Reg.x19,.x20,.x21,.x22,.x25,.x26], z ∉ rs) : StreamAt a s pt n h u := by
  have g (z : Reg) (hz : z ∈ [Reg.x19,.x20,.x21,.x22,.x25,.x26]) := r.others _ (keep _ hz)
  exact ⟨p.env.keep (fun z hz => g z (List.mem_append_left [Reg.x22,.x25,.x26] hz)) r.sp r.rd r.wr,
    (g _ (by decide)).trans p.x22,(g _ (by decide)).trans p.offset,(g _ (by decide)).trans p.dst,
    r.rd.trans p.rd,r.wr.trans p.wr,by rw [r.mem]; exact p.ctr,by rw [r.mem]; exact p.out,p.hashBound,
    by rw [r.mem]; exact p.hashPtr,by rw [r.mem]; exact p.y,by rw [r.mem]; exact p.frame⟩

abbrev batchDone (stitch : Bool) (n : Nat) := if stitch && decide (batchTest n ≠ 0) then VG.Proof.AesGcm.AArch64.Stitch.pre n else 0
abbrev hashedAfter (stitch : Bool) (n T h : Nat) :=
  if stitch && decide (batchTest n ≠ 0) then (T+batchDone stitch n)/16 else h

theorem PieceAt.batch_exact (v : GcmImpl) (stitch : Bool) (p : PieceAt a s i j h t) (pr : PiecesPre a s) (hi : i < a.count)
    (whole : len a s i-j=0 ∨ pos a s i j%16=0) (gh : stitch = true → GatherLaws) :
    WP isa (if stitch then batches v.callees else .block []) t fun u =>
      let j' := j+batchDone stitch (len a s i-j)
      let h' := hashedAfter stitch (len a s i-j) (pos a s i j) h
      PieceAt a s i j' h' u ∧ (len a s i-j'=0 ∨ pos a s i j'%16=0) := by
  cases stitch
  · exact WP.block_nil ⟨p,whole⟩
  let T := pos a s i j
  let n := len a s i-j
  have inc := p.inputs pr hi
  have lim := pieceBound a s hi
  have bound := p.le
  have Tn : T+n ≤ a.total s := by dsimp [T,n,pos]; omega_arith
  have hash := p.hashBound
  change 16*h ≤ T at hash
  obtain ⟨dst,apart,_⟩ := inc.outAt
  have input : BatchIn a.Wn a.Ctx a.St a.W a.SP (atOff (frag a s i) j) (atOff a.dst T) a.R n t :=
    ⟨p.env,pr.rounds,p.x22,p.src,p.rest,p.dst,inc.data,dst,apart⟩
  by_cases rem : n=0
  · have z : batchTest n = 0 := by rw [rem]; decide
    refine (batches_ok (k := 0) (P := a.dst) v input pr.lay (gh rfl) (fun hz => False.elim (hz z))).mono fun u hu => ?_
    rcases hu with ⟨_,r⟩|⟨hz,_⟩
    · change batchTest (len a s i-j) = 0 at z
      simp only [batchDone,hashedAfter,z,ne_eq,not_true_eq_false,decide_false,Bool.and_false,Bool.false_eq_true,ite_false,Nat.add_zero]
      refine ⟨⟨p.toStreamAt.ofRegs r (by decide),bound,(r.others _ (by decide)).trans p.src,
        (r.others _ (by decide)).trans p.rest,(r.others _ (by decide)).trans p.desc,
        (r.others _ (by decide)).trans p.count⟩,whole⟩
    · exact False.elim (hz z)
  have aligned : T%16 = 0 := whole.resolve_left rem
  let k := T/16-h
  have size : T=16*(h+k) := by dsimp [k]; omega_arith
  have pend : PendingIn a.Wn a.St a.W (atOff a.dst (16*h)) (atOff a.dst T) k t := by
    refine ⟨p.hashPtr,?_,?_⟩
    · simp only [atOff,Offset.add_add]; congr 2; omega_arith
    · exact (((pr.dst.ok.drop (by omega_arith : 16*h ≤ a.total s)).take
        (by omega_arith : 16*k ≤ a.total s-16*h)).of_eq p.rd p.wr)
  have base := (pr.dst.take Tn).of_eq p.rd p.wr
  have cip := p.cipher pr (by change T ≤ a.total s; omega_arith)
  have ctx := textApart pr (pr.dst.ctx.sub_right (Region.sub_prefix (by omega_arith : T ≤ a.total s))) pr.lay.cs pr.lay.cw'
  have hashkey : Spec.Gcm.ctxH t.mem a.Ctx = Spec.Gcm.ctxH s.mem a.Ctx := blockAt_frame p.frame
    (fun r hr => (ctx r hr).sub_left (Lay.ctxSub (by decide)))
  have ctr : VG.Proof.Gcm.Ctr t.mem (a.St+48) (a.St+64) (a.ciph t) a.icb T := by rw [cip]; exact p.ctr
  refine (batches_ok v input pr.lay (gh rfl) (fun _ => pend)).mono fun u hu => ?_
  obtain ⟨b,hh,be,he,q⟩ := batches_progress input pr.lay size rfl base (hashkey ▸ p.y) ctr p.hashPtr hu
  have le := q.le
  change b ≤ len a s i-j at le
  have div := q.whole
  have endAl : (T+b)%16=0 := by obtain ⟨z,hz⟩ := div; omega_arith
  have eqb : batchDone true n = b := by by_cases zz : batchTest n = 0 <;> simp [be,batchDone,zz]
  have eqh : hashedAfter true n T h = hh := by by_cases zz : batchTest n = 0 <;> simp [he,be,batchDone,hashedAfter,zz]
  change PieceAt a s i (j+batchDone true n) (hashedAfter true n T h) u ∧ _
  rw [eqb,eqh]
  refine ⟨p.advance pr hi (by omega_arith) q.env
    ((q.saved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.x22) ?_
    q.src q.dst q.rest (q.saved _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (q.saved _ (by decide) (by decide) (by decide) (by decide) (by decide)) q.rd q.wr q.ctr q.data
    q.hashed q.hashPtr (by rw [← hashkey]; exact q.y) q.frame,Or.inr ?_⟩
  · rw [q.saved _ (by decide) (by decide) (by decide) (by decide) (by decide),p.offset]
    change BitVec.ofNat 64 (T%16) = BitVec.ofNat 64 ((T+b)%16)
    rw [aligned,endAl]
  · simpa [T,pos,Nat.add_assoc] using endAl

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! The generic gather loop, including empty descriptors, arbitrary splits
of a counter block, and interleaved authentication of long fragments. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (batches aligned leftover pieces)
open VG.Proof.Gcm.AArch64.Stitch (GatherLaws)
open VG.Proof.AesGcm.AArch64.Gather (sb sl gl_succ pt_succ gl_mono)
variable {a : TextArgs} {s t : State} {i h : Nat}

abbrev decodeCode : List Instr := [.ldr .x .x23 .x27 0,.ldr .x .x24 .x27 8,ptr .x27 .x27 16]

theorem decode_ok (p : TextAt a s i h t) (pr : PiecesPre a s) (hi : i < a.count) :
    WP isa (.block decodeCode) t (PieceAt a s i 0 h) := by
  have bound : a.gl s i ≤ a.total s := gl_mono _ _ (Nat.le_of_lt hi)
  have sep := textApart pr (pr.apart.sub_right (Region.sub_prefix bound)) pr.desc.st pr.desc.w
  have lenLt := pr.descLt
  have get (d : Nat) (hd : d + 8 ≤ 16*a.count) : InRegions (t.rd++t.wr) (atOff a.src d) 8 := by
    rw [p.rd,p.wr]; exact pr.desc.rd _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hd (by omega_arith)⟩
  have fixed (d : Nat) (hd : d + 8 ≤ 16*a.count) :
      t.mem.readW (atOff a.src d) 64 = s.mem.readW (atOff a.src d) 64 :=
    p.frame.readW (r := ⟨a.src,16*a.count⟩) (Offset.contains_base _ hd (by omega_arith)) sep (by decide)
  have g0 : InRegions (t.rd++t.wr) (t.gpr .x27 + BitVec.ofNat 64 0) 8 := by rw [p.desc,BitVec.add_zero]; exact get _ (by omega_arith)
  have g8 : InRegions (t.rd++t.wr) (t.gpr .x27 + BitVec.ofNat 64 8) 8 := by
    rw [p.desc,atOff,Offset.add_add]; exact get _ (by omega_arith)
  obtain ⟨u,run,x23,x24,x27,r⟩ : ∃ u, runBlock isa decodeCode t = some u ∧ u.gpr .x23 = frag a s i ∧
      u.gpr .x24 = BitVec.ofNat 64 (len a s i) ∧ u.gpr .x27 = atOff a.src (16*(i+1)) ∧ Regs [.x23,.x24,.x27] t u := by
    refine ⟨_, by arun [decodeCode,g0,g8],?_⟩
    refine ⟨?_,?_,?_,⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩
    · simp only [gpr_write,ite_false,reduceCtorEq,ite_true,BitVec.setWidth_eq,BitVec.add_zero,p.desc]
      exact fixed _ (by omega_arith)
    · simp only [gpr_write,ite_false,reduceCtorEq,ite_true,BitVec.setWidth_eq,p.desc]
      change t.mem.readW (atOff a.src (16*i) + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (s.mem.readW _ 64).toNat
      simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq,atOff,Offset.add_add]
      exact fixed _ (by omega_arith)
    · simp [gpr_write,p.desc,atOff,Offset.add_add,Nat.mul_add]
  refine WP.of_runBlock ⟨u,run,⟨?_,Nat.zero_le _,by simpa [atOff] using x23,x24,x27,
    (r.others _ (by decide)).trans p.count⟩⟩
  simpa [plain,pos,Spec.Aes.bytesAt] using p.toStreamAt.ofRegs r (by decide)

theorem count_ok (p : PieceAt a s i (len a s i) h t) (hi : i < a.count) :
    WP isa (.block [.subImm .x .x28 .x28 1]) t (TextAt a s (i+1) h) := by
  obtain ⟨u,run,x28,r⟩ : ∃ u, runBlock isa [.subImm .x .x28 .x28 1] t = some u ∧
      u.gpr .x28 = BitVec.ofNat 64 (a.count-(i+1)) ∧ Regs [.x28] t u := by
    refine ⟨_,by arun [],?_⟩
    refine ⟨?_,⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩
    simp only [gpr_write,ite_true,BitVec.setWidth_eq,p.count]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  refine WP.of_runBlock ⟨u,run,⟨?_,(r.others _ (by decide)).trans p.desc,x28⟩⟩
  have eqpt : a.pt s (i+1) = plain a s i (len a s i) := pt_succ _ _ _
  have eqn : a.gl s (i+1) = pos a s i (len a s i) := gl_succ _ _ _
  rw [eqpt,eqn]
  exact p.toStreamAt.ofRegs r (by decide)

abbrev body (v : GcmImpl) (stitch : Bool) : Prog isa :=
  .seq (.block decodeCode) <| .seq leftover <| .seq (if stitch then batches v.callees else .block []) <|
    .seq (.ite (.zero .x .x24) (.block []) (aligned v.callees)) (.block [.subImm .x .x28 .x28 1])

abbrev nextHash (stitch : Bool) (off n h : Nat) :=
  let z := crHead (off%16) n
  hashedAfter stitch (n-z) (off+z) h

theorem body_exact (v : GcmImpl) (stitch : Bool) (pr : PiecesPre a s) (hi : i < a.count) (p : TextAt a s i h t)
    (hv : v.ctr.scratch ≤ a.Wn-512) (gh : stitch = true → GatherLaws) :
    WP isa (body v stitch) t (TextAt a s (i+1) (nextHash stitch (a.gl s i) (len a s i) h)) := by
  refine WP.seq ((decode_ok p pr hi).mono fun _ d => WP.seq ((d.head_exact pr hi).mono fun _ ⟨e,whole⟩ =>
    WP.seq ((e.batch_exact v stitch pr hi whole gh).mono fun _ ⟨f,whole'⟩ =>
    WP.seq ((f.tail v pr hi whole' hv).mono fun _ g => by simpa only [nextHash,pos,Nat.add_zero,Nat.zero_add,Nat.sub_zero] using count_ok g hi))))

def hashCount (stitch : Bool) (a : TextArgs) (s : State) : Nat → Nat
  | 0 => 0
  | i+1 => nextHash stitch (a.gl s i) (len a s i) (hashCount stitch a s i)

theorem pieces_exact (v : GcmImpl) (stitch : Bool) (pr : PiecesPre a s)
    (hv : v.ctr.scratch ≤ a.Wn-512) (gh : stitch = true → GatherLaws) :
    WP isa (pieces v.callees stitch) s (TextAt a s a.count (hashCount stitch a s a.count)) := by
  have lt := pr.descLt
  refine WP.ite _ (eval_zero pr.x28 (by omega_arith)) (fun z => ?_) (fun nz => ?_)
  · exact WP.block_nil (by simpa only [of_decide_eq_true z, hashCount] using TextAt.start pr)
  · have hn := of_decide_eq_false nz
    refine WP.loop (M := isa) (body := body v stitch) (c := .nonzero .x .x28)
      (fun k t => ∃ i, k = a.count-i ∧ i < a.count ∧ TextAt a s i (hashCount stitch a s i) t) ?_ a.count s
      ⟨0,rfl,by omega_arith,TextAt.start pr⟩
    rintro k u ⟨i,rfl,hi,p⟩
    refine (body_exact v stitch pr hi p hv gh).mono fun w step => ?_
    have ev := eval_nonzero step.count (by omega_arith)
    by_cases he : i+1=a.count
    · exact .inl ⟨by rw [ev,he]; simp,by change TextAt a s (i+1) (hashCount stitch a s (i+1)) w at step; simpa only [he] using step⟩
    · exact .inr ⟨by rw [ev]; simp; omega_arith,a.count-(i+1),by omega_arith,i+1,rfl,by omega_arith,step⟩

theorem pieces_ok (v : GcmImpl) (stitch : Bool) (pr : PiecesPre a s)
    (hv : v.ctr.scratch ≤ a.Wn-512) (gh : stitch = true → GatherLaws) :
    WP isa (pieces v.callees stitch) s fun t => ∃ h, TextAt a s a.count h t :=
  (pieces_exact v stitch pr hv gh).mono fun _ p => ⟨_,p⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic
