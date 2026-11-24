module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.CachedFront
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.PrepKey
public import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Prepared AES and AES/SHA3 records use the same entry and argument slots.
The saved source and destination remain independent throughout the record. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous

abbrev word (W : Addr) (i : Nat) : Addr := W + BitVec.ofNat 64 i
abbrev slotR (W : Addr) (i : Nat) : Region := ⟨word W i,8⟩

structure Entry (wn : Nat) (o t : State) (W : Addr) : Prop where
  env : Env wn (o.gpr .x0) (word W 16) W o.sp t
  x22 : t.gpr .x22 = o.gpr .x1
  x23 : t.gpr .x23 = o.gpr .x2
  x28 : t.gpr .x28 = stackArg o 1
  x4 : t.gpr .x4 = o.gpr .x4
  x5 : t.gpr .x5 = o.gpr .x5
  x6 : t.gpr .x6 = o.gpr .x6
  x7 : t.gpr .x7 = stackArg o 0
  alen : t.mem.readW (word W 224) 64 = o.gpr .x5
  src : t.mem.readW (word W 232) 64 = o.gpr .x6
  len : t.mem.readW (word W 240) 64 = stackArg o 0
  dst : t.mem.readW (word W 320) 64 = o.gpr .x7
  saved : SavedAt t.mem W o
  frame : Frame [workR wn W] o.mem t.mem
  rd : t.rd = o.rd
  wr : t.wr = o.wr

/-- Save the ABI registers, then keep only the slots actually read by the
prepared record. The tag stays in x28 throughout. -/
theorem entry_ok {wn : Nat} {o : State} {W : Addr} (hW : stackArg o 3 = W)
    (access : ∀ i < 4, InRegions (o.rd++o.wr) (stackArgAddr o i) 8)
    (sep : ∀ i < 2, (slotR o.sp (8*i)).Disjoint (workR wn W)) (perm : Perm wn (o.gpr .x0) (word W 16) W o) :
    WP isa (.block preparedArgs) o (Entry wn o · W) := by
  obtain bounds := perm.hWn
  obtain ⟨a,ra,x9,ga,sa,ma,da,wa⟩ := ldrSp_ok (t := .x9) (k := 24) (by decide) hW (access 3 (by decide))
  obtain ⟨b,rb,gb,sb,db,wb,mb⟩ := save_ok a .x9 x9 (wa ▸ perm.w) (by omega)
  unfold preparedArgs
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.of_runBlock ⟨a,ra,?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b,rb,?_⟩
  have g (r : Reg) (h : r ≠ .x9) : b.gpr r = o.gpr r := by rw [gb,ga _ h]
  have base : b.gpr .x9 = W := by rw [gb,x9]
  have st := sb.trans sa
  have rd := db.trans da
  have wr := wb.trans wa
  have write (d : Nat) (h : d+8 ≤ wn) : InRegions b.wr (word W d) 8 := by rw [wr]; exact in_off perm.w h (by omega)
  have read (i : Nat) (h : i<2) : InRegions (b.rd++b.wr) (word b.sp (8*i)) 8 := by
    rw [st,rd,wr]; exact access i (by omega)
  have savedFr : Frame [workR wn W] o.mem b.mem := by
    rw [mb,ma]
    exact (savedMem_frame _ _ _).sub fun r hr => ⟨_,.head _,List.mem_singleton.mp hr ▸ Offset.sub_base _ (by omega)⟩
  let m := ((b.mem.writeW (word W 224) (o.gpr .x5)).writeW (word W 232) (o.gpr .x6)).writeW (word W 320) (o.gpr .x7)
  let m' := m.writeW (word W 240) (stackArg o 0)
  let slots : Region := ⟨word W 224,104⟩
  have contains (d : Nat) (l : 224≤d) (h : d+8≤328) : slots.Contains (word W d) 8 :=
    Offset.contains W l (by omega) (by decide)
  have fm : Frame [slots] b.mem m := (((Frame.refl _ _).writeW (.head _) _ (contains 224 (by decide) (by decide))).writeW
    (.head _) _ (contains 232 (by decide) (by decide))).writeW (.head _) _ (contains 320 (by decide) (by decide))
  have fm' : Frame [slots] b.mem m' := fm.writeW (.head _) _ (contains 240 (by decide) (by decide))
  have combine {mem : Mem} (f : Frame [slots] b.mem mem) : Frame [workR wn W] o.mem mem :=
    savedFr.trans (f.sub fun r hr => ⟨_,.head _,List.mem_singleton.mp hr ▸ Offset.sub_base W (by omega)⟩)
  have stackRead {mem : Mem} (f : Frame [slots] b.mem mem) (i : Nat) (h : i<2) :
      mem.readW (word b.sp (8*i)) 64 = stackArg o i := by
    rw [st]
    exact (combine f).readW (r := slotR o.sp (8*i)) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using sep i h) (by decide)
  have r0 := read 0 (by decide)
  have r1 := read 1 (by decide)
  have n := stackRead fm 0 (by decide)
  have tag := stackRead fm' 1 (by decide)
  change InRegions _ (b.sp+0#64) 8 at r0
  change InRegions _ (b.sp+8#64) 8 at r1
  rw [BitVec.add_zero] at r0
  change m.read (b.sp+0#64) 8 = _ at n
  change m'.read (b.sp+8#64) 8 = _ at tag
  rw [BitVec.add_zero] at n
  let t := ((((((b.write .x .x19 W).write .x .x20 (word W 16)).write .x .x21 (o.gpr .x0)).write .x .x22
    (o.gpr .x1)).write .x .x7 (stackArg o 0)).write .x .x23 (o.gpr .x2)).write .x .x28 (stackArg o 1)
  have w1 := write 224 (by omega)
  have w2 := write 232 (by omega)
  have w3 := write 320 (by omega)
  have w4 := write 240 (by omega)
  simp only [word,Mem.writeW,BitVec.setWidth_eq,m',m] at w1 w2 w3 w4 n tag
  refine WP.of_runBlock ⟨{t with mem := m'},?_,?_⟩
  · arun [t,m',m,word,alenO,dataO,dstO,lenO,base,Mem.writeW,w1,w2,w3,w4,r0,r1,n,tag,BitVec.add_zero,
      g .x0 (by decide),g .x1 (by decide),g .x2 (by decide),g .x5 (by decide),g .x6 (by decide),g .x7 (by decide)]
  constructor
  · exact ⟨by simp [t,gpr_write],by simp [t,gpr_write],by simp [t,gpr_write],st,perm.of_eq rd wr⟩
  all_goals try (solve | simp [t,gpr_write,g])
  · unfold m' m word
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
  · unfold m' m word
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
  · exact Mem.readW_writeW_self64 ..
  · unfold m' m word
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
  · have saved : SavedAt b.mem W o := by
      rw [mb,ma]; exact fun p hp => (savedMem_slot _ _ _ p hp).trans (ga _ ((by decide : ∀ p ∈ VG.Impl.AesGcm.AArch64.saved, p.1 ≠ .x9) p hp))
    exact saved.frame fm' fun r hr => List.mem_singleton.mp hr ▸ Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact combine fm'
  · exact rd
  · exact wr

open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH blockAt)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)

open VG.Impl.Gcm.AArch64.Pmull (C tReg sReg poly loadPw pwOff)
open VG.Proof.Gcm.AArch64.Pmull (keyV pp)

abbrev FirstPower := ∀ H, keyV H = pp H 1

theorem cachedKey_ok {u : State} {P : Addr} {H : Spec.Gcm.Block}
    (ptr : u.gpr .x8 = P)
    (take : InRegions (u.rd++u.wr) (P+16#64) 16) (key : u.mem.read (P+16#64) 16 = keyV H) :
    WP isa (.block cachedKey) u fun z => Fast.HKey H z ∧ Regs [.x0,.x5,.x6,.x7] u z := by
  have off : pwOff 1 = 16 := by decide
  refine WP.of_runBlock ⟨_,by unfold cachedKey; arun [off,ptr,take],?_⟩
  refine ⟨⟨?_,?_,?_⟩,⟨?_,rfl,rfl,rfl,rfl⟩⟩
  · simp [v_setV,gpr_write]; rfl
  · simpa [v_setV,v_write,tReg,sReg,C] using key
  · simp [v_setV,v_write,tReg,sReg,C]; rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp [gpr_setV,gpr_write,hr.2.1]

abbrev withPower (s : State) (p : Addr) := s.write .x .x8 p

theorem powerPtr_ok {wn : Nat} {o s : State} {W : Addr} (e : Entry wn o s W)
    (slot : InRegions (o.rd++o.wr) (stackArgAddr o 2) 8) (sep : (slotR o.sp 16).Disjoint (workR wn W)) :
    WP isa (.block [.ldrSp .x8 16]) s fun t => t = withPower s (stackArg o 2) := by
  have a : InRegions (s.rd++s.wr) (s.sp+16#64) 8 := by rw [e.rd,e.wr,e.env.sp]; exact slot
  have k : s.mem.read (s.sp+16#64) 8 = stackArg o 2 := by
    rw [e.env.sp]
    exact e.frame.readW (r := slotR o.sp 16) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using sep) (by decide)
  exact WP.of_runBlock ⟨_,by arun [a,k],rfl⟩

theorem front_ok {wn : Nat} {o s : State} {W : Addr} (L : Lay wn (o.gpr .x0) (word W 16) W)
    (mul : MulKey) (preparedKey : FirstPower) (e : Entry wn o s W) (ha : (o.gpr .x5).toNat ≤ 16)
    (nonce : DataOk wn (word W 16) W o (o.gpr .x2) 12)
    (aad : DataOk wn (word W 16) W o (o.gpr .x4) (o.gpr .x5).toNat)
    (slot : InRegions (o.rd++o.wr) (stackArgAddr o 2) 8) (disSlot : (slotR o.sp 16).Disjoint (workR wn W))
    (powers : GhWCall o (o.gpr .x0) (word (word W 16) 16) (word W 512) (stackArg o 2))
    (disP : (⟨stackArg o 2,128⟩ : Region).Disjoint (workR wn W))
    (sub : ∀ r ∈ j0Frame (word W 16) W, r.Sub (workR wn W)) :
    WP isa cachedFront s
      (Fast.FFront wn (o.gpr .x0) (word W 16) W o.sp (ctxH o.mem (o.gpr .x0))
        (bytesAt o.mem (o.gpr .x2) 12) (bytesAt o.mem (o.gpr .x4) (o.gpr .x5).toNat)
        (o.gpr .x6) (stackArg o 0).toNat s) := by
  have hh : blockAt s.mem (word (o.gpr .x0) 240) = ctxH o.mem (o.gpr .x0) :=
    blockAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using (L.cw'.sub_left (Offset.sub_base (o.gpr .x0) (by decide : 240 + 16 ≤ 256))))
  refine WP.seq ((powerPtr_ok e slot disSlot).mono ?_)
  rintro _ rfl
  let u := withPower s (stackArg o 2)
  have g : Regs [.x8] s u := ⟨by
    intro r hr
    have ne : r ≠ .x8 := by simpa only [List.mem_singleton] using hr
    simp [u,withPower,gpr_write,ne],rfl,rfl,rfl,rfl⟩
  have j : FixedNonceIn wn (o.gpr .x0) (word W 16) W o.sp u.gpr (ctxH o.mem (o.gpr .x0)) (o.gpr .x2) u :=
    ⟨e.env.of_regs g,fun _ _ => rfl,e.x23,nonce.of_eq e.rd e.wr,hh⟩
  have nonceBytes : bytesAt s.mem (o.gpr .x2) 12 = bytesAt o.mem (o.gpr .x2) 12 :=
    bytesAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using nonce.w) (by decide)
  have aadBytes : bytesAt s.mem (o.gpr .x4) (o.gpr .x5).toNat = bytesAt o.mem (o.gpr .x4) (o.gpr .x5).toNat :=
    bytesAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using aad.w) (Nat.le_of_lt (o.gpr .x5).isLt)
  rw [← nonceBytes,← aadBytes]
  apply WP.mono (Q := Fast.FFront _ _ _ _ _ _ _ _ _ _ u) (Q' := _) (s := u) (c := Impl.AesGcm.AArch64.Fast.frontWith cachedKey)
  · refine Fast.frontWith_ok L cachedKey mul (n := (stackArg o 0).toNat) j (aad.of_eq e.rd e.wr) ha e.x4 (by simpa [u,withPower,gpr_write] using e.x5) e.x6
      (by simpa [u,withPower,gpr_write] using e.x7) ?_
    intro t _ _ f rd wr x8
    have frame : Frame [workR wn W] o.mem t.mem := e.frame.trans (f.sub fun r h => ⟨_,.head _,sub r h⟩)
    have access : (⟨stackArg o 2,128⟩ : Region).Contains (stackArg o 2 + 16#64) 16 :=
      Offset.contains_base _ (by decide) (by decide)
    refine cachedKey_ok (P := stackArg o 2) (x8.trans (by simp [u,withPower,gpr_write])) ?_ ?_
    · rw [rd,wr]; change InRegions (s.rd++s.wr) _ _; rw [e.rd,e.wr]
      exact powers.reads _ _ ⟨_,.head _,access⟩
    · rw [preparedKey]
      have old := (powers.repr 0 (by decide)).2
      exact (frame.read (r := ⟨stackArg o 2,128⟩) access
        (by simpa only [List.mem_singleton,forall_eq] using disP) (by decide)).trans old
  · intro t h
    exact ⟨h.env,h.x22,h.x28,h.x23,h.x26,h.hH,h.j0,h.cb,h.y,h.key,h.frame,h.rd,h.wr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
