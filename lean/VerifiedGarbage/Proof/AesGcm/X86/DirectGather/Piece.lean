module

public import VerifiedGarbage.Impl.AesGcm.X86.DirectGather
public import VerifiedGarbage.Proof.AesGcm.X86.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Crypt
import VerifiedGarbage.Proof.Framework.Offset

/-! The gather loop's public descriptor count, kept in the scratch frame. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86

variable {N : Nat}

open VG.Impl.AesGcm.X86.DirectGather (descriptor setCursors nextPiece headArgs headDone partialHead)

def afterDescriptor (m : Mem) (W S D : BitVec 32) (n : BitVec 32) : Mem :=
  (((m.writeW (w64 W+168#64) D).writeW (w64 W+172#64) n).writeW
    (w64 W+276#64) n).writeW (w64 W+196#64) (S+8#32)

/-- Read one eight-byte IA-32 descriptor and advance the next-descriptor slot. -/
theorem descriptor_ok {C St W SP S D n : BitVec 32} {K : Nat} {s : State} (L : Lay N C St W SP K)
    (e : Env N C St W SP s) (ptr : slotv s.mem W rO = S) (src : s.mem.readW (w64 S) 32 = D)
    (size : s.mem.readW (w64 (S+4#32)) 32 = n) (r₀ : InRegions (s.rd++s.wr) (w64 S) 4)
    (r₄ : InRegions (s.rd++s.wr) (w64 (S+4#32)) 4)
    (apart : Mem.Sep (w64 (S+4#32)) 4 (w64 W+168#64) 4) :
    WP isa (.block descriptor) s fun t => t.mem = afterDescriptor s.mem W S D n ∧ t.gpr .ecx = n ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have length : (s.mem.writeW (w64 W+168#64) D).readW (w64 (S+4#32)) 32 = n :=
    (Mem.readW_writeW_sep apart (by decide)).trans size
  refine WP.of_runBlock ⟨_,by xrun [descriptor,e.ebp,L.aW,e.wIn,e.wIn',ptr,add_zero32,r₀,r₄,src,length],?_⟩
  refine ⟨rfl,rfl,?_,rfl,rfl⟩
  intro r a c d
  simp [gpr_setMem,gpr_setReg,a,c,d]

def afterCursors (m : Mem) (W SP D off n : BitVec 32) : Mem :=
  ((m.writeW (w64 SP) (D+off)).writeW (w64 W+160#64) (n+off)).writeW
    (w64 W+280#64) (off &&& 15#32)

/-- The destination address is the start of the output plus all prior piece lengths.
The saved counter offset and the condition flag come from that same public sum. -/
theorem setCursors_ok {C St W SP D off n : BitVec 32} {K : Nat} {s : State} (L : Lay N C St W SP K)
    (e : Env N C St W SP s) (total : slotv s.mem W xlO = off) (count : s.gpr .ecx = n)
    (ar : InRegions (s.rd++s.wr) (w64 (SP+28#32)) 4) (arg : s.mem.readW (w64 (SP+28#32)) 32 = D)
    (wr : InRegions s.wr (w64 SP) 4) :
    WP isa (.block setCursors) s fun t =>
      t.mem = afterCursors s.mem W SP D off n ∧ t.gpr .edi = D+off ∧
      t.zf = some (off &&& 15#32 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.of_runBlock ⟨_,by xrun [setCursors,e.ebp,e.esp,L.aW,e.wIn,e.wIn',total,count,ar,arg,wr,add_zero32],?_⟩
  refine ⟨?_,?_,rfl,?_,rfl,rfl⟩
  · change ((s.mem.writeW _ (off+D)).writeW _ _).writeW _ _ = _
    rw [BitVec.add_comm off D]; rfl
  · exact BitVec.add_comm off D
  · intro r a d c
    simp [gpr_setMem,gpr_setReg,a,d,c]

/-- An argument outside the scratch workspace survives the descriptor loads. -/
private theorem descriptor_arg {m : Mem} {W S D n : BitVec 32} {A : Addr}
    (apart : (⟨A,4⟩ : Region).Disjoint ⟨w64 W,N⟩) (hN : 768 ≤ N := by wbig) :
    (afterDescriptor m W S D n).readW A 32 = m.readW A 32 := by
  have sep (d : Nat) (hd : d + 4 ≤ 768) : Mem.Sep A 4 (w64 W + BitVec.ofNat 64 d) 4 :=
    (apart.sub_right (Lay.wSub hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  simp only [afterDescriptor,Mem.readW_writeW_sep (w:=32) (w':=32) (sep 196 (by decide)) (by decide),
    Mem.readW_writeW_sep (w:=32) (w':=32) (sep 276 (by decide)) (by decide),
    Mem.readW_writeW_sep (w:=32) (w':=32) (sep 172 (by decide)) (by decide),
    Mem.readW_writeW_sep (w:=32) (w':=32) (sep 168 (by decide)) (by decide)]

theorem nextPiece_ok {C St W SP S D O off n : BitVec 32} {K : Nat} {s : State}
    (L : Lay N C St W SP K) (e : Env N C St W SP s) (ptr : slotv s.mem W rO = S)
    (src : s.mem.readW (w64 S) 32 = D) (size : s.mem.readW (w64 (S+4#32)) 32 = n)
    (r₀ : InRegions (s.rd++s.wr) (w64 S) 4) (r₄ : InRegions (s.rd++s.wr) (w64 (S+4#32)) 4)
    (apart : Mem.Sep (w64 (S+4#32)) 4 (w64 W+168#64) 4)
    (total : slotv s.mem W xlO = off) (ar : InRegions (s.rd++s.wr) (w64 (SP+28#32)) 4)
    (arg : s.mem.readW (w64 (SP+28#32)) 32 = O) (wr : InRegions s.wr (w64 SP) 4)
    (aw : (⟨w64 (SP+28#32),4⟩ : Region).Disjoint ⟨w64 W,N⟩) :
    WP isa (.block nextPiece) s fun t =>
      t.mem = afterCursors (afterDescriptor s.mem W S D n) W SP O off n ∧ t.gpr .edi = O+off ∧
      t.zf = some (off &&& 15#32 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.block_append
  refine WP.mono (descriptor_ok L e ptr src size r₀ r₄ apart) ?_
  rintro u ⟨mem,cx,regs,rd,uwr⟩
  have keep (d : Nat) (hd : d + 4 ≤ 168) : slotv u.mem W d = slotv s.mem W d := by
    rw [mem]
    simp only [slotv,afterDescriptor, readW_writeW_off _ _ _ (a:=d) (b:=196) (Or.inl (by omega_using [hd])) (by omega_using [hd]) (by decide),
      readW_writeW_off _ _ _ (a:=d) (b:=276) (Or.inl (by omega_using [hd])) (by omega_using [hd]) (by decide),
      readW_writeW_off _ _ _ (a:=d) (b:=172) (Or.inl (by omega_using [hd])) (by omega_using [hd]) (by decide),
      readW_writeW_off _ _ _ (a:=d) (b:=168) (Or.inl hd) (by omega_using [hd]) (by decide)]
  have env := e.keep (regs .ebp (by decide) (by decide) (by decide))
    (regs .esi (by decide) (by decide) (by decide)) (regs .esp (by decide) (by decide) (by decide))
    rd uwr (keep ctxO (by decide))
  refine WP.mono (setCursors_ok (D:=O) L env ((keep xlO (by decide)).trans total) cx
    (by rw [rd,uwr]; exact ar) (by rw [mem,descriptor_arg aw]; exact arg) (by rw [uwr]; exact wr)) ?_
  rintro t ⟨m,di,z,rs,r,w⟩
  exact ⟨m.trans (by rw [mem]),di,z,fun q a b c d => (rs q a b c).trans (regs q a c d),
    r.trans rd,w.trans uwr⟩

/-- Prepare the source, destination, and keystream pointers for a piece starting
within a counter block, and save the number of bytes still to encrypt. -/
theorem headArgs_ok {C St W SP D T : BitVec 32} {K n b k : Nat} {s : State} (L : Lay N C St W SP K)
    (e : Env N C St W SP s) (hb : slotv s.mem W bO = BitVec.ofNat 32 b)
    (hn : slotv s.mem W lenO = BitVec.ofNat 32 n) (hd : slotv s.mem W dataO = D)
    (cx : s.gpr .ecx = BitVec.ofNat 32 k) (di : s.gpr .edi = T) (hk : k ≤ n) (hlt : n < 2^32) :
    WP isa (.block headArgs) s fun t => t.mem = s.mem.writeW (w64 W+172#64) (BitVec.ofNat 32 (n-k)) ∧
      t.gpr .edx = St+64#32+BitVec.ofNat 32 b ∧ t.gpr .esi = D ∧ t.gpr .edi = T ∧
      t.gpr .ecx = BitVec.ofNat 32 k ∧ t.gpr .ebp = W ∧ t.gpr .esp = SP ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.of_runBlock ⟨_,by xrun [headArgs,e.ebp,e.esi,L.aW,e.wIn,e.wIn',hb,hn,hd,cx],?_⟩
  refine ⟨?_,rfl,rfl,di,cx,e.ebp,e.esp,rfl,rfl⟩
  exact congrArg (fun x => s.mem.writeW (w64 W+172#64) x) (ofNat_sub32 hk hlt)

theorem headDone_ok {s : State} {W SP D T : BitVec 32} (bp : s.gpr .ebp = W) (sp : s.gpr .esp = SP)
    (si : s.gpr .esi = D) (di : s.gpr .edi = T) (fit : W.toNat+N ≤ 2^32)
    (wD : InRegions s.wr (w64 W+168#64) 4) (wT : InRegions s.wr (w64 SP) 4) (hN : 768 ≤ N := by wbig) :
    WP isa (.block headDone) s fun t => t.mem = (s.mem.writeW (w64 W+168#64) D).writeW (w64 SP) T ∧
      t.gpr .esi = W+16#32 ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have a : w64 (W+168#32) = w64 W+168#64 := w64_add (by omega_using [fit, (by wbig : 768 ≤ N)])
  refine WP.of_runBlock ⟨_,by xrun [headDone,bp,sp,si,di,a,wD,wT,add_zero32],?_⟩
  refine ⟨rfl,rfl,?_,rfl,rfl⟩
  intro r h
  simp [gpr_setMem,gpr_setReg,h]

abbrev headKey (St : BitVec 32) (b : Nat) := St+64#32+BitVec.ofNat 32 b

/-- Memory after consuming a nonempty suffix of the retained keystream block. -/
def afterHead (m : Mem) (W SP St D T : BitVec 32) (n b k : Nat) : Mem :=
  let m₁ := m.writeW (w64 W+172#64) (BitVec.ofNat 32 (n-k))
  let m₂ := VG.WriteBytes.writeBytes m₁ (w64 T) (xorBytes m₁ (w64 D) (w64 (headKey St b)) k)
  (m₂.writeW (w64 W+168#64) (D+BitVec.ofNat 32 k)).writeW (w64 SP) (T+BitVec.ofNat 32 k)

structure HeadAccess (s : State) (St SP D T : BitVec 32) (b k : Nat) : Prop where
  fK : (headKey St b).toNat+k ≤ 2^32
  fS : D.toNat+k ≤ 2^32
  fD : T.toNat+k ≤ 2^32
  rd : Covers [⟨w64 (headKey St b),k⟩] (s.rd++s.wr)
  rdS : Covers [⟨w64 D,k⟩] (s.rd++s.wr)
  wr : Covers [⟨w64 T,k⟩] s.wr
  stack : InRegions s.wr (w64 SP) 4
  disj : (⟨w64 (headKey St b),k⟩ : Region).Disjoint ⟨w64 T,k⟩
  sd : D = T ∨ (⟨w64 D,k⟩ : Region).Disjoint ⟨w64 T,k⟩

theorem partialHead_ok {C St W SP D T : BitVec 32} {K n b : Nat} {s : State}
    (L : Lay N C St W SP K) (e : Env N C St W SP s) (hs : W+16#32 = St)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 n) (hb : slotv s.mem W bO = BitVec.ofNat 32 b)
    (len : slotv s.mem W lenO = BitVec.ofNat 32 n) (src : slotv s.mem W dataO = D)
    (di : s.gpr .edi = T) (hb16 : b < 16) (hlt : n < 2^32)
    (access : HeadAccess s St SP D T b (min (16-b) n)) :
    WP isa partialHead s fun t =>
      t.mem = (if min (16-b) n = 0 then s.mem else afterHead s.mem W SP St D T n b (min (16-b) n)) ∧
      t.gpr .ebp = W ∧ t.gpr .esp = SP ∧ t.gpr .esi = St ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let k := min (16-b) n
  have kn : k ≤ n := Nat.min_le_right _ _
  have kl : k < 2^32 := Nat.lt_of_le_of_lt kn hlt
  refine WP.seq (WP.mono (minLen_ok L e hn hb (Nat.le_of_lt hb16) hlt) ?_)
  intro u hu
  obtain env := e.keep (hu.other .ebp (by decide) (by decide)) (hu.other .esi (by decide) (by decide))
    (hu.other .esp (by decide) (by decide)) hu.rd hu.wr (by rw [hu.mem])
  refine WP.seq (WP.of_runBlock ⟨_,by xrun [hu.ecx],?_⟩)
  refine WP.ite (decide (k=0)) (and_self_beq32 kl |> congrArg some) (fun z => ?_) (fun nz => ?_)
  · have zk : k = 0 := by simpa using z
    refine WP.block_nil ⟨?_,env.ebp,env.esp,env.esi,hu.rd,hu.wr⟩
    change u.mem = if k = 0 then s.mem else _
    rw [ite_eq_left zk,hu.mem]
  · have pk : 0 < k := by
      have ne : k ≠ 0 := by simpa using nz
      exact Nat.pos_of_ne_zero ne
    have kd : k ≠ 0 := Nat.ne_of_gt pk
    refine WP.seq (WP.mono (headArgs_ok L (s:=_) (e:=?_) (D:=D) (T:=T) (k:=k)
      (by change slotv u.mem W bO = _; rw [hu.mem,hb]) (by change slotv u.mem W lenO = _; rw [hu.mem,len])
      (by change slotv u.mem W dataO = _; rw [hu.mem,src]) hu.ecx ((hu.other _ (by decide) (by decide)).trans di) kn hlt) ?_)
    · exact ⟨env.ebp,env.esi,env.esp,env.ctxR,env.stW,env.wW,env.ctx⟩
    rintro v ⟨m,dx,si,di',cx,bp,sp,rd,wr⟩
    have rd₁ : v.rd = s.rd := rd.trans hu.rd
    have wr₁ : v.wr = s.wr := wr.trans hu.wr
    have hx : XorPreG true v (headKey St b) D T k :=
      ⟨dx,di',si,(fun h => nomatch h),cx,pk,kl,access.fK,access.fS,access.fD,by rw [rd₁,wr₁]; exact access.rd,
       by rw [rd₁,wr₁]; exact access.rdS,by rw [wr₁]; exact access.wr,access.disj,access.sd⟩
    refine WP.seq (WP.mono (xorLoopG_ok true v hx) ?_)
    intro x h
    have bp' := (h.other .ebp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans bp
    have sp' := (h.other .esp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sp
    refine WP.mono (headDone_ok bp' sp' (h.esi rfl) h.edi L.fw
      (by rw [h.wr,wr₁]; exact e.wIn (by decide)) (by rw [h.wr,wr₁]; exact access.stack)) ?_
    rintro t ⟨mt,st,g,rt,wt⟩
    refine ⟨?_,(g .ebp (by decide)).trans bp',(g .esp (by decide)).trans sp',st.trans hs,
      rt.trans (h.rd.trans rd₁),wt.trans (h.wr.trans wr₁)⟩
    change t.mem = if k = 0 then s.mem else _
    rw [ite_eq_right kd,mt,h.mem,m]
    change _ = afterHead s.mem W SP St D T n b k
    rw [← hu.mem]
    rfl

theorem decrement_ok {C St W SP : BitVec 32} {K n : Nat} {s : State} (L : Lay N C St W SP K)
    (e : Env N C St W SP s) (hn : 0 < n) (lt : n < 2^32)
    (v : slotv s.mem W tglO = BitVec.ofNat 32 n) :
    WP isa (.block [.mov .ecx (slot tglO),.alu .sub .ecx (imm 1),.store (at_ .ebp tglO) .ecx]) s fun t =>
      t.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 tglO) (BitVec.ofNat 32 (n-1)) ∧
      t.zf = some (decide (n=1)) ∧ (∀ r, r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have sub : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n-1) := ofNat_sub32 hn lt
  refine WP.of_runBlock ⟨_,by xrun [e.ebp,L.aW,e.wIn,e.wIn',v],?_⟩
  refine ⟨?_,?_,?_,rfl,rfl⟩
  · exact congrArg (fun x => s.mem.writeW (w64 W + BitVec.ofNat 64 tglO) x) sub
  · exact congrArg some (sub_beq32 lt (by decide : 1 < 2^32))
  · intro r h
    simp [gpr_setMem,gpr_setReg,h]


end VG.Proof.AesGcm.X86.DirectGather

end

/-! The bytes from a previous fragment's saved keystream. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (xorKs)

variable {N : Nat}

abbrev atByte (p : BitVec 32) (i : Nat) := p+BitVec.ofNat 32 i
abbrev headFrame (W SP T : BitVec 32) (k : Nat) : List Region :=
  [⟨w64 T,k⟩,⟨w64 W+168#64,8⟩,⟨w64 SP,4⟩]

structure HeadPost (m u : Mem) (St W SP D T : BitVec 32) (ciph : Block → Block) (icb : Block)
    (off n k : Nat) : Prop where
  frame : Frame (headFrame W SP T k) m u
  out : bytesAt u (w64 T) k = xorKs ciph icb off (bytesAt m (w64 D) k)
  ctr : CtrS u St ciph icb (off+k)
  src : slotv u W dataO = atByte D k
  len : slotv u W lenO = BitVec.ofNat 32 (n-k)
  dest : u.readW (w64 SP) 32 = atByte T k

theorem afterHead_ok {C St W SP D T : BitVec 32} {m : Mem} {ciph : Block → Block} {icb : Block}
    {off n k : Nat} (L : Lay N C St W SP 32) (st : St = W+16#32) (P : PieceRegions N C W SP D T n)
    (ctr : CtrS m St ciph icb off) (b0 : off%16 ≠ 0) (kb : off%16+k ≤ 16) (kn : k ≤ n) :
    HeadPost m (afterHead m W SP St D T n (off%16) k) St W SP D T ciph icb off n k := by
  let b := off%16
  let m₁ := m.writeW (w64 W+172#64) (BitVec.ofNat 32 (n-k))
  let K := headKey St b
  let xs := xorBytes m₁ (w64 D) (w64 K) k
  let m₂ := WriteBytes.writeBytes m₁ (w64 T) xs
  let m₃ := (m₂.writeW (w64 W+168#64) (atByte D k)).writeW (w64 SP) (atByte T k)
  have kl : k < 2^64 := by omega_using [kb]
  obtain dt := P.dstWork.sub_left (Region.sub_prefix kn)
  have xt : xs.length = k := length_xorBytes _ _ _ _
  have f₁ : Frame [⟨w64 W+172#64,4⟩] m m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₂ : Frame [⟨w64 T,k⟩] m₁ m₂ := writeBytes_frame' _ xt
  have f₃ : Frame [⟨w64 W+168#64,4⟩,⟨w64 SP,4⟩] m₂ m₃ := by
    exact ((Frame.refl [⟨w64 W+168#64,4⟩,⟨w64 SP,4⟩] m₂).writeW (List.mem_cons_self ..) (atByte D k) (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (atByte T k) (Region.contains_self _ _)
  have frame : Frame (headFrame W SP T k) m m₃ :=
    ((f₁.sub (fun x hx => by
       simp only [List.mem_singleton] at hx; subst hx
       exact ⟨⟨w64 W+168#64,8⟩,by simp [headFrame],Offset.sub _ (by decide) (by decide)⟩)).trans
     (f₂.sub (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩))).trans
     (f₃.sub (fun x hx => by
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
       rcases hx with rfl | rfl
       · exact ⟨⟨w64 W+168#64,8⟩,by simp [headFrame],Region.sub_prefix (by decide)⟩
       · exact ⟨⟨w64 SP,4⟩,by simp [headFrame],fun _ h => h⟩))
  have sw := stSub L st
  have pSt {d : Nat} (hd : d+16 ≤ 80) : ∀ r ∈ headFrame W SP T k, (⟨w64 St+BitVec.ofNat 64 d,16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (dt.sub_right (fun _ h => sw _ (Lay.stSub hd _ h))).symm
    · exact L.st_w hd (.inr ⟨by decide,by decide⟩)
    · exact (P.argWork.sub_right (fun _ h => sw _ (Lay.stSub hd _ h))).symm
  have keys : w64 K = w64 St+64#64+BitVec.ofNat 64 b := by
    change w64 (St+64#32+BitVec.ofNat 32 b) = _
    rw [w64_add (by rw [L.nS (by decide)]; have f := L.fs; dsimp [b]; omega_using [f]),L.aS (by decide)]
  have s0 : bytesAt m₁ (w64 D) k = bytesAt m (w64 D) k :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (P.srcWork.sub_left (Region.sub_prefix kn)).sub_right (Lay.wSub (by decide))) (by omega_using [kl])
  have k0 : bytesAt m₁ (w64 K) k = bytesAt m (w64 K) k := by
    rw [keys,BitVec.add_assoc,←BitVec.ofNat_add]
    refine bytesAt_frame f₁ (fun r hr => ?_) (by omega_using [kl])
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w (by dsimp [b]; omega_using [kb]) (.inr ⟨by decide,by decide⟩)
  have output : bytesAt m₃ (w64 T) k = xs := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl
      · exact dt.sub_right (Lay.wSub (by decide))
      · exact (P.argDst.sub_right (Region.sub_prefix kn)).symm) (by omega_using [kl])]
    simpa only [xt] using bytesAt_writeBytes_self m₁ (w64 T) xs (by rw [xt]; exact kl)
  change HeadPost m m₃ St W SP D T ciph icb off n k
  refine ⟨frame,?_,(ctr.head b0 kb).congr (blockAt_frame frame (pSt (d:=48) (by decide)))
    (blockAt_frame frame (pSt (d:=64) (by decide))),?_,?_,Mem.readW_writeW_self32 _ _ _⟩
  · rw [output]
    dsimp only [xs,xorBytes]
    rw [s0,k0,keys]
    have c := VG.Proof.Gcm.ctr_head ctr b0 (d:=bytesAt m (w64 D) k) (by rw [length_bytesAt]; exact kb)
    simpa only [length_bytesAt] using c
  · exact (Mem.readW_writeW_sep (((P.argWork.sub_right (Lay.wSub (d:=168) (n:=4) (by decide))).symm).sep
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)).trans (Mem.readW_writeW_self32 _ _ _)
  · have h : slotv m₂ W lenO = slotv m₁ W lenO :=
      slot_frame f₂ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (dt.sub_right (Lay.wSub (by decide))).symm)
    have pr : slotv m₃ W lenO = slotv m₂ W lenO := slot_frame f₃ (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact (P.argWork.sub_right (Lay.wSub (by decide))).symm)
    exact pr.trans (h.trans (Mem.readW_writeW_self32 _ _ _))

def headCount (off n : Nat) := if off%16=0 then 0 else min (16-off%16) n

structure PieceArgs (N : Nat) (C St W SP D T : BitVec 32) (s : State) (n off : Nat) : Prop where
  env : Env N C St W SP s
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  bO : slotv s.mem W bO = BitVec.ofNat 32 (off%16)
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  src : slotv s.mem W dataO = D
  di : s.gpr .edi = T
  zf : s.zf = some (decide (off%16=0))

theorem noHead {s : State} {C St W SP D T : BitVec 32} {n off : Nat} {ciph : Block → Block} {icb : Block}
    (h : PieceArgs N C St W SP D T s n off) (A : PieceAccess s SP D T n) (ctr : CtrS s.mem St ciph icb off) :
    HeadPost s.mem s.mem St W SP D T ciph icb off n 0 := by
  exact ⟨Frame.refl _ _,rfl,ctr,by simpa [atByte] using h.src,h.len,by simpa [atByte] using A.dstArg⟩

theorem makeHeadAccess {C St W SP D T : BitVec 32} {n b k : Nat} {s : State} (L : Lay N C St W SP 32)
    (st : St = W+16#32) (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n)
    (E : Env N C St W SP s) (wsp : InRegions s.wr (w64 SP) 4) (bl : b < 16) (hb : b+k ≤ 16) (kn : k ≤ n) :
    HeadAccess s St SP D T b k := by
  have fw := L.fs
  have fd := P.fD
  have ft := P.fT
  have key : w64 (headKey St b) = w64 St+BitVec.ofNat 64 (64+b) := by
    unfold headKey
    rw [BitVec.add_assoc,←BitVec.ofNat_add,w64_add (by omega_using [bl,fw])]
  have sk : Region.Sub ⟨w64 (headKey St b),k⟩ ⟨w64 W,N⟩ := by
    rw [key]; exact fun _ hx => stSub L st _ (Lay.stSub (by omega_using [hb]) _ hx)
  refine ⟨?_,by omega_using [fd,kn],by omega_using [ft,kn],?_,covers_pre A.rd kn (by omega_using [fd]),
    covers_pre A.wr kn (by omega_using [ft]),wsp,((P.dstWork.sub_left (Region.sub_prefix kn)).sub_right sk).symm,
    P.srcDst.imp id (fun hd => (hd.sub_left (Region.sub_prefix kn)).sub_right (Region.sub_prefix kn))⟩
  · unfold headKey
    rw [BitVec.add_assoc,←BitVec.ofNat_add,toNat_add32 (by omega_using [fw,bl])]; omega_using [fw,hb]
  · rw [key]; exact covers_left (E.stC (by omega_using [hb]))

theorem headPart_ok {C St W SP D T : BitVec 32} {s : State} {n off : Nat} {ciph : Block → Block} {icb : Block}
    (L : Lay N C St W SP 32) (st : St = W+16#32) (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n)
    (h : PieceArgs N C St W SP D T s n off) (wr : InRegions s.wr (w64 SP) 4) (lt : n < 2^32)
    (ctr : CtrS s.mem St ciph icb off) :
    WP isa (.ite .e (.block []) Impl.AesGcm.X86.DirectGather.partialHead) s fun t =>
      HeadPost s.mem t.mem St W SP D T ciph icb off n (headCount off n) ∧
      t.gpr .ebp = W ∧ t.gpr .esi = St ∧ t.gpr .esp = SP ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.ite (decide (off%16=0)) h.zf (fun z => ?_) (fun nz => ?_)
  · have zero : off%16 = 0 := by simpa using z
    rw [headCount,ite_eq_left zero]
    exact WP.block_nil ⟨noHead h A ctr,h.env.ebp,h.env.esi,h.env.esp,rfl,rfl⟩
  · have nonzero : off%16 ≠ 0 := by simpa using nz
    let k := min (16-off%16) n
    have kn : k ≤ n := Nat.min_le_right _ _
    have kb : off%16+k ≤ 16 := by dsimp [k]; omega_using []
    have access := makeHeadAccess L st P A h.env wr (by omega_using []) kb kn
    rw [headCount,ite_eq_right nonzero]
    refine WP.mono (partialHead_ok L h.env st.symm h.nO h.bO h.len h.src h.di (by omega_using []) lt access) ?_
    rintro t ⟨m,bp,sp,si,rd,w⟩
    refine ⟨?_,bp,si,sp,rd,w⟩
    by_cases hz : k=0
    · change t.mem = (if k=0 then s.mem else _) at m
      rw [ite_eq_left hz] at m
      change HeadPost _ _ _ _ _ _ _ _ _ _ _ k
      rw [hz,m]; exact noHead h A ctr
    · change t.mem = (if k=0 then s.mem else _) at m
      rw [ite_eq_right hz] at m
      rw [m]; exact afterHead_ok L st P ctr nonzero kb kn

end VG.Proof.AesGcm.X86.DirectGather

end

/-! Process one gather piece from any byte position in the counter stream. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Gcm (Block)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)

variable {N : Nat}

abbrev pieceFrame (N : Nat) (St W SP T : BitVec 32) (n : Nat) : List Region :=
  crFrame N St W SP 32 T n ++ [⟨w64 W+168#64,8⟩,⟨w64 SP,4⟩]

structure Processed (N : Nat) (C St W SP D T : BitVec 32) (s : State) (off n : Nat) (ciph : Block → Block) (icb : Block)
    (t : State) : Prop where
  env : Env N C St W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (pieceFrame N St W SP T n) s.mem t.mem
  ctr : CtrS t.mem St ciph icb (off+n)
  out : bytesAt t.mem (w64 T) n = xorKs ciph icb off (bytesAt s.mem (w64 D) n)

section
variable {C St W SP D T : BitVec 32} {n off k : Nat} {s u t : State} {ciph : Block → Block} {icb : Block}
  (L : Lay N C St W SP 32) (st : St = W+16#32) (P : PieceRegions N C W SP D T n)
  (A : PieceAccess s SP D T n) (h : HeadPost s.mem u.mem St W SP D T ciph icb off n k)

include P in
theorem restRegions (hk : k<n) : PieceRegions N C W SP (atByte D k) (atByte T k) (n-k) := by
  have fd := P.fD
  have ft := P.fT
  have d : w64 (atByte D k) = w64 D+BitVec.ofNat 64 k := w64_add (by omega_using [fd,hk])
  have t : w64 (atByte T k) = w64 T+BitVec.ofNat 64 k := w64_add (by omega_using [ft,hk])
  have ds : Region.Sub ⟨w64 (atByte D k),n-k⟩ ⟨w64 D,n⟩ := by rw [d]; exact Offset.sub_base _ (by omega_using [hk])
  have ts : Region.Sub ⟨w64 (atByte T k),n-k⟩ ⟨w64 T,n⟩ := by rw [t]; exact Offset.sub_base _ (by omega_using [hk])
  exact ⟨P.srcWork.sub_left ds,P.dstWork.sub_left ts,P.dstCtx.sub_right ts,P.srcDst.imp (congrArg (fun p => atByte p k)) (fun hd => (hd.sub_left ds).sub_right ts),
    P.stackSrc.sub_right ds,P.stackDst.sub_right ts,P.argWork,P.argDst.sub_right ts,P.fSP,
    by unfold atByte; rw [toNat_add32 (by omega_using [fd,hk])]; omega_using [fd,hk],
    by unfold atByte; rw [toNat_add32 (by omega_using [ft,hk])]; omega_using [ft,hk]⟩

include A h P in
theorem restAccess (hk : k<n) (rd : u.rd=s.rd) (wr : u.wr=s.wr) :
    PieceAccess u SP (atByte D k) (atByte T k) (n-k) := by
  have fd := P.fD
  have ft := P.fT
  exact ⟨h.dest,by rw [rd,wr]; exact A.argR,
    by rw [rd,wr,w64_add (x:=D) (by omega_using [fd,hk])]; exact covers_off A.rd (by omega_using [hk]) (by omega_using [fd]),
    by rw [wr,w64_add (x:=T) (by omega_using [ft,hk])]; exact covers_off A.wr (by omega_using [hk]) (by omega_using [ft])⟩

include P in
theorem slotHead {o : Nat} (ho : o+4 ≤ 168 ∨ 176 ≤ o) (fit : o+4 ≤ 768) (kn : k≤n) (hN : 768 ≤ N := by wbig) :
    ∀ r ∈ headFrame W SP T k, (⟨w64 W+BitVec.ofNat 64 o,4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((P.dstWork.sub_left (Region.sub_prefix kn)).sub_right (Lay.wSub fit)).symm
  · exact Lay.w_w ho fit (by decide)
  · exact (P.argWork.sub_right (Lay.wSub fit)).symm

include h in
theorem pieceFrameHead (kn : k ≤ n) : Frame (pieceFrame N St W SP T n) s.mem u.mem := by
  refine h.frame.sub ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨w64 T,n⟩,by simp [pieceFrame,crFrame],Region.sub_prefix kn⟩
  · exact ⟨_,by simp [pieceFrame],fun _ q => q⟩
  · exact ⟨_,by simp [pieceFrame],fun _ q => q⟩

include P in
theorem pieceFrameRest (hk : k<n) {m m' : Mem} (f : Frame (crFrame N St W SP 32 (atByte T k) (n-k)) m m') :
    Frame (pieceFrame N St W SP T n) m m' := by
  refine f.sub ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 T,n⟩,by simp [pieceFrame,crFrame],by
      rw [w64_add (x:=T) (by have h := P.fT; omega_using [h,hk])]
      exact Offset.sub_base _ (by omega_using [hk])⟩
  all_goals exact ⟨_,by simp [pieceFrame,crFrame],fun _ q => q⟩

include L st P A h in
theorem restDone (hk : k<n) (rd : u.rd=s.rd) (wr : u.wr=s.wr)
    (hstk : (⟨w64 D,n⟩ : Region).Disjoint ⟨w64 SP,4⟩)
    (done : PiecePost N u C St W SP (atByte D k) (atByte T k) ciph icb (off+k) (n-k) t) :
    Processed N C St W SP D T s off n ciph icb t := by
  have fd := P.fD
  have ft := P.fT
  have diff : k+(n-k)=n := by omega_using [hk]
  have da : w64 (atByte D k) = w64 D+BitVec.ofNat 64 k := w64_add (by omega_using [fd,hk])
  have ta : w64 (atByte T k) = w64 T+BitVec.ofNat 64 k := w64_add (by omega_using [ft,hk])
  have prev : bytesAt t.mem (w64 T) k = bytesAt u.mem (w64 T) k := by
    refine bytesAt_frame done.frame ?_ (by omega_using [hk,ft])
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [ta]; exact split_disj (by omega_using [hk,ft])
    · exact ((A.dataW L st P).ok.st.sub_left (Region.sub_prefix (Nat.le_of_lt hk))).sub_right (Lay.stSub (by decide))
    · exact (P.dstWork.sub_left (Region.sub_prefix (Nat.le_of_lt hk))).sub_right (Lay.wsSub)
    · exact (P.stackDst.sub_right (Region.sub_prefix (Nat.le_of_lt hk))).symm
  have source : bytesAt u.mem (w64 (atByte D k)) (n-k) = bytesAt s.mem (w64 (atByte D k)) (n-k) := by
    have sub : Region.Sub ⟨w64 (atByte D k),n-k⟩ ⟨w64 D,n⟩ := by rw [da]; exact Offset.sub_base _ (by omega_using [hk])
    refine bytesAt_frame h.frame ?_ (by omega_using [hk,fd])
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases P.srcDst with rfl | hd
      · rw [da]; exact (split_disj (by omega_using [hk,ft])).symm
      exact (hd.sub_left sub).sub_right (Region.sub_prefix (Nat.le_of_lt hk))
    · exact (P.srcWork.sub_left sub).sub_right (Lay.wSub (by decide))
    · exact hstk.sub_left sub
  refine ⟨done.env,done.rd.trans rd,done.wr.trans wr,(pieceFrameHead h (Nat.le_of_lt hk)).trans
    (pieceFrameRest P hk done.frame),by simpa only [Nat.add_assoc,diff] using done.ctr,?_⟩
  have tail := done.out
  rw [source,ta,da] at tail
  conv => lhs; rw [←diff,bytesAt_add]
  conv => rhs; rw [←diff,bytesAt_add]
  rw [Proof.Gcm.xorKs_append,length_bytesAt,prev,h.out,tail]

end

/-- Encrypt the piece from the current byte offset. Readable inputs and
writable outputs have distinct addresses throughout both stages. -/
theorem processPiece_ok (v : GcmImpl) [WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {n off R : Nat} {s : State}
    {ciph : Block → Block} {icb : Block} (L : Lay N C St W SP 32) (st : St = W+16#32)
    (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n) (args : PieceArgs N C St W SP D T s n off)
    (argCtx : (⟨w64 C,256⟩ : Region).Disjoint ⟨w64 SP,4⟩)
    (argWr : InRegions s.wr (w64 SP) 4) (hstk : (⟨w64 D,n⟩ : Region).Disjoint ⟨w64 SP,4⟩) (lt : n < 2^32)
    (rounds : RoundsAt s.mem W R) (cipher : ciphOf s.mem C R = ciph) (ctr : CtrS s.mem St ciph icb off) :
    WP isa (.seq (.ite .e (.block []) Impl.AesGcm.X86.DirectGather.partialHead) (Open.decTo v.callees v.callees.ctr))
      s (Processed N C St W SP D T s off n ciph icb) := by
  let k := headCount off n
  have kn : k ≤ n := by unfold k headCount; split <;> first | exact Nat.zero_le _ | exact Nat.min_le_right _ _
  refine WP.seq (WP.mono (headPart_ok L st P A args argWr lt ctr) ?_)
  rintro u ⟨h,bp,si,sp,rd,wr⟩
  have slot (o : Nat) (sep : o+4 ≤ 168 ∨ 176 ≤ o) (bound : o+4 ≤ 768) :
      slotv u.mem W o = slotv s.mem W o := slot_frame h.frame (slotHead P sep bound kn)
  have e := args.env.keep (bp.trans args.env.ebp.symm) (si.trans args.env.esi.symm) (sp.trans args.env.esp.symm)
    rd wr (slot ctxO (by decide) (by decide))
  by_cases hk : k = n
  · have z : n-k=0 := by omega_using [hk]
    have len := h.len
    change _ = BitVec.ofNat 32 (n-k) at len
    rw [z] at len
    refine WP.mono (decTo_empty L v e len) ?_
    rintro t ⟨m,bp',si',sp',rt,wt⟩
    have et := e.keep (bp'.trans bp.symm) (si'.trans si.symm) (sp'.trans sp.symm) rt wt (by rw [m])
    refine ⟨et,rt.trans rd,wt.trans wr,by rw [m]; exact pieceFrameHead h kn,?_,?_⟩
    · rw [m,←hk]; exact h.ctr
    · rw [m,←hk]; exact h.out
  · have less : k<n := by omega_using [kn,hk]
    have r : RoundsAt u.mem W R := ⟨(slot roundsO (by decide) (by decide)).trans rounds.1,rounds.2⟩
    have c : ciphOf u.mem C R = ciph := by
      rw [ciph_frame h.frame (fun x hx => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact P.dstCtx.sub_right (Region.sub_prefix kn)
        · exact L.cw.sub_right (Lay.wSub (by decide))
        · exact argCtx) rounds.2,cipher]
    have align : (off+k)%16=0 := by
      by_cases hb : off%16=0
      · simp [k,headCount,hb]
      · simp only [k,headCount,ite_eq_right hb] at less ⊢
        have eq : min (16-off%16) n = 16-off%16 := Nat.min_eq_left (by omega_using [less])
        rw [eq]
        omega_using [hb]
    refine WP.mono (decTo_ok L st (restRegions P less) v e (restAccess P A h less rd wr) r h.src h.len
      (by omega_using [lt]) (fun _ => align) c h.ctr) ?_
    intro t result
    exact restDone L st P A h less rd wr hstk result

/-- A zero-length listed slice can contain any pointer, including when prior
pieces end exactly at the end of the IA-32 address space. -/
theorem headEmpty_ok {C St W SP D T : BitVec 32} {off : Nat} {s : State}
    (L : Lay N C St W SP 32) (args : PieceArgs N C St W SP D T s 0 off) :
    WP isa (.ite .e (.block []) Impl.AesGcm.X86.DirectGather.partialHead) s fun t =>
      t.mem = s.mem ∧ Env N C St W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  refine WP.ite (decide (off%16=0)) args.zf (fun _ => WP.block_nil ⟨rfl,args.env,rfl,rfl⟩) ?_
  intro _
  refine WP.seq (WP.mono (minLen_ok L args.env args.nO args.bO (by omega_using []) (by decide)) ?_)
  intro u h
  have e := args.env.keep (h.other .ebp (by decide) (by decide)) (h.other .esi (by decide) (by decide))
    (h.other .esp (by decide) (by decide)) h.rd h.wr (by rw [h.mem])
  have cx : u.gpr .ecx=0#32 := by simpa only [Nat.min_zero] using h.ecx
  refine WP.seq (WP.of_runBlock ⟨_,by xrun [cx],?_⟩)
  exact WP.ite true rfl (fun _ => WP.block_nil ⟨h.mem,⟨e.ebp,e.esi,e.esp,e.ctxR,e.stW,e.wW,e.ctx⟩,h.rd,h.wr⟩) (fun h => nomatch h)

theorem processPiece_empty (v : GcmImpl) {C St W SP D T : BitVec 32} {off : Nat} {s : State}
    (L : Lay N C St W SP 32) (args : PieceArgs N C St W SP D T s 0 off) :
    WP isa (.seq (.ite .e (.block []) Impl.AesGcm.X86.DirectGather.partialHead) (Open.decTo v.callees v.callees.ctr))
      s fun t => t.mem = s.mem ∧ Env N C St W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  refine WP.seq (WP.mono (headEmpty_ok L args) ?_)
  rintro u ⟨m,e,rd,wr⟩
  refine WP.mono (decTo_empty L v e (by rw [m,args.len]; rfl)) ?_
  rintro t ⟨mt,bp,si,sp,rt,wt⟩
  exact ⟨mt.trans m,e.keep (bp.trans e.ebp.symm) (si.trans e.esi.symm) (sp.trans e.esp.symm)
    rt wt (by rw [mt]),rt.trans rd,wt.trans wr⟩

end VG.Proof.AesGcm.X86.DirectGather

end
