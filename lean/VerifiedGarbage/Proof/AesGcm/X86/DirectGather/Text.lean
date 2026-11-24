module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Piece
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
import VerifiedGarbage.Proof.Gcm.SealGather

/-! The descriptor cursor, cumulative length, and the remaining count. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.Impl.AesGcm.X86

abbrev setup (m : Mem) (W SP S D O : BitVec 32) (off n : Nat) :=
  afterCursors (afterDescriptor m W S D (BitVec.ofNat 32 n)) W SP O (BitVec.ofNat 32 off) (BitVec.ofNat 32 n)

abbrev setupFrame (W SP : BitVec 32) : List Region :=
  [⟨w64 W+160#64,4⟩,⟨w64 W+168#64,8⟩,⟨w64 W+196#64,4⟩,⟨w64 W+276#64,8⟩,⟨w64 SP,4⟩]

structure SetupSlots (m : Mem) (W SP S D O : BitVec 32) (off n : Nat) : Prop where
  total : slotv m W xlO = BitVec.ofNat 32 (off+n)
  src : slotv m W dataO = D
  len : slotv m W lenO = BitVec.ofNat 32 n
  ptr : slotv m W rO = S+8#32
  nO : slotv m W nO = BitVec.ofNat 32 n
  bO : slotv m W bO = BitVec.ofNat 32 (off%16)
  arg : m.readW (w64 SP) 32 = O+BitVec.ofNat 32 off

theorem setupFrame_ok (m : Mem) (W SP S D O : BitVec 32) (off n : Nat) :
    Frame (setupFrame W SP) m (setup m W SP S D O off n) := by
  unfold setup afterDescriptor afterCursors
  apply Frame.writeW (r:=⟨w64 W+276#64,8⟩) _ (by simp [setupFrame]) _ (Offset.contains _ (by decide) (by decide) (by decide))
  apply Frame.writeW (r:=⟨w64 W+160#64,4⟩) _ (by simp [setupFrame]) _ (Region.contains_self _ _)
  apply Frame.writeW (r:=⟨w64 SP,4⟩) _ (by simp [setupFrame]) _ (Region.contains_self _ _)
  apply Frame.writeW (r:=⟨w64 W+196#64,4⟩) _ (by simp [setupFrame]) _ (Region.contains_self _ _)
  apply Frame.writeW (r:=⟨w64 W+276#64,8⟩) _ (by simp [setupFrame]) _ (Offset.contains _ (by decide) (by decide) (by decide))
  apply Frame.writeW (r:=⟨w64 W+168#64,8⟩) _ (by simp [setupFrame]) _ (Offset.contains _ (by decide) (by decide) (by decide))
  apply Frame.writeW (r:=⟨w64 W+168#64,8⟩) _ (by simp [setupFrame]) _ (Offset.contains _ (by decide) (by decide) (by decide))
  exact Frame.refl _ _

theorem setupSlots (m : Mem) (W SP S D O : BitVec 32) {off n : Nat} (flt : off<2^32)
    (argW : (⟨w64 SP,4⟩ : Region).Disjoint ⟨w64 W,2560⟩) : SetupSlots (setup m W SP S D O off n) W SP S D O off n := by
  have sep (d : Nat) (hd : d+4 ≤ 2560) : Mem.Sep (w64 SP) 4 (w64 W+BitVec.ofNat 64 d) 4 :=
    (argW.sub_right (Lay.wSub hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have sep' (d : Nat) (hd : d+4 ≤ 2560) : Mem.Sep (w64 W+BitVec.ofNat 64 d) 4 (w64 SP) 4 :=
    (argW.sub_right (Lay.wSub hd)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain mask := and15 (BitVec.ofNat 32 off)
  rw [toNat_ofNat32 flt] at mask
  constructor
  all_goals
    simp (disch:=decide) only [slotv,setup,afterCursors,afterDescriptor,xlO,dataO,lenO,rO,nO,bO,
      readW_writeW_off,Mem.readW_writeW_self32,Mem.readW_writeW_sep (w:=32) (w':=32) (sep 280 (by decide)) (by decide),
      Mem.readW_writeW_sep (w:=32) (w':=32) (sep 160 (by decide)) (by decide),
      Mem.readW_writeW_sep (w:=32) (w':=32) (sep' 168 (by decide)) (by decide),
      Mem.readW_writeW_sep (w:=32) (w':=32) (sep' 172 (by decide)) (by decide),
      Mem.readW_writeW_sep (w:=32) (w':=32) (sep' 196 (by decide)) (by decide),
      Mem.readW_writeW_sep (w:=32) (w':=32) (sep' 276 (by decide)) (by decide),mask]
  rw [ofNat_add_ofNat32,Nat.add_comm]

end VG.Proof.AesGcm.X86.DirectGather

end

/-! The stream invariant across the public array of IA-32 gather descriptors. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Gcm (Block gatheredLen gathered)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)
open VG.Proof.AesGcm.X86.Gather (sb sl)

structure Text where
  C : BitVec 32
  W : BitVec 32
  SP : BitVec 32
  Src : BitVec 32
  O : BitVec 32
  count : Nat
  len : Nat
  rounds : Nat

namespace Text
abbrev st (a : Text) := a.W+16#32
abbrev off (a : Text) (m : Mem) (i : Nat) := gatheredLen 32 m (w64 a.Src) i
abbrev buf (a : Text) (m : Mem) (i : Nat) := gathered 32 m (w64 a.Src) i
abbrev source (a : Text) (m : Mem) (i : Nat) := sb m a.Src i
abbrev size (a : Text) (m : Mem) (i : Nat) := sl m a.Src i
abbrev desc (a : Text) (i : Nat) := atByte a.Src (8*i)
abbrev dstArg (a : Text) := w64 (a.SP+28#32)

abbrev frame (a : Text) (l : Nat) : List Region :=
  crFrame a.st a.W a.SP 32 a.O l ++
  [⟨w64 a.SP,4⟩,⟨w64 a.W+160#64,4⟩,⟨w64 a.W+168#64,8⟩,⟨w64 a.W+180#64,4⟩,⟨w64 a.W+196#64,4⟩]

structure Outside (a : Text) (X : Region) : Prop where
  w : X.Disjoint ⟨w64 a.W,2560⟩
  sp : X.Disjoint ⟨w64 a.SP,4⟩
  stack : X.Disjoint (below a.SP 32)

theorem Outside.frame {a : Text} (L : Lay a.C a.st a.W a.SP 32) {X : Region} (h : Outside a X) {n : Nat}
    (d : X.Disjoint ⟨w64 a.O,n⟩) : ∀ r ∈ a.frame n, X.Disjoint r := by
  intro r hr
  simp only [Text.frame,crFrame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · exact d
  · exact h.w.sub_right (fun _ q => stSub L rfl _ (Lay.stSub (by decide) _ q))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.stack
  · exact h.sp
  all_goals exact h.w.sub_right (Lay.wSub (by decide))

theorem Outside.setup {a : Text} {X : Region} (h : Outside a X) : ∀ r ∈ setupFrame a.W a.SP, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr => exact h.sp
  all_goals exact h.w.sub_right (Lay.wSub (by decide))

theorem setup_sub {m u : Mem} (a : Text) (n : Nat) (f : Frame (setupFrame a.W a.SP) m u) :
    Frame (a.frame n) m u := by
  refine f.sub ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inl =>
    exact ⟨wsR a.W,by simp [frame,crFrame],Offset.sub _ (by decide) (by decide)⟩
  all_goals exact ⟨_,by simp [frame,crFrame],fun _ q => q⟩

theorem frame_mono {m u : Mem} (a : Text) {n k : Nat} (le : k≤n) (f : Frame (a.frame k) m u) :
    Frame (a.frame n) m u := by
  refine f.sub ?_
  intro r hr
  simp only [frame,crFrame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 a.O,n⟩,by simp [frame,crFrame],Region.sub_prefix le⟩
  all_goals exact ⟨_,by simp [frame,crFrame],fun _ q => q⟩

end Text

structure TextInput (a : Text) (s : State) : Prop where
  lay : Lay a.C a.st a.W a.SP 32
  env : Env a.C a.st a.W a.SP s
  rounds : RoundsAt s.mem a.W a.rounds
  total : a.off s.mem a.count = a.len
  countLt : a.count < 2^32
  lenLt : a.len < 2^32
  descFit : a.Src.toNat+a.count*8 ≤ 2^32
  dstFit : a.O.toNat+a.len ≤ 2^32
  descR : Covers [⟨w64 a.Src,a.count*8⟩] (s.rd++s.wr)
  srcR : ∀ i < a.count, Covers [⟨w64 (a.source s.mem i),a.size s.mem i⟩] (s.rd++s.wr)
  srcFit : ∀ i < a.count, (a.source s.mem i).toNat+a.size s.mem i ≤ 2^32
  dstW : Covers [⟨w64 a.O,a.len⟩] s.wr
  descOutside : a.Outside ⟨w64 a.Src,a.count*8⟩
  srcOutside : ∀ i < a.count, a.Outside ⟨w64 (a.source s.mem i),a.size s.mem i⟩
  dstOutside : a.Outside ⟨w64 a.O,a.len⟩
  argOutside : a.Outside ⟨a.dstArg,4⟩
  descDst : (⟨w64 a.Src,a.count*8⟩ : Region).Disjoint ⟨w64 a.O,a.len⟩
  srcDst : ∀ i < a.count, (⟨w64 (a.source s.mem i),a.size s.mem i⟩ : Region).Disjoint ⟨w64 a.O,a.len⟩
  argDst : (⟨a.dstArg,4⟩ : Region).Disjoint ⟨w64 a.O,a.len⟩
  ctxDst : (⟨w64 a.C,256⟩ : Region).Disjoint ⟨w64 a.O,a.len⟩
  argCtx : (⟨w64 a.C,256⟩ : Region).Disjoint ⟨w64 a.SP,4⟩
  argW : (⟨w64 a.SP,4⟩ : Region).Disjoint ⟨w64 a.W,2560⟩
  spFit : a.SP.toNat+4 ≤ 2^32
  spW : Covers [⟨w64 a.SP,4⟩] s.wr
  argR : InRegions (s.rd++s.wr) a.dstArg 4
  arg : s.mem.readW a.dstArg 32 = a.O

structure TextAt (a : Text) (s : State) (icb : Block) (i : Nat) (u : State) : Prop where
  env : Env a.C a.st a.W a.SP u
  rd : u.rd=s.rd
  wr : u.wr=s.wr
  ptr : slotv u.mem a.W rO = a.desc i
  count : slotv u.mem a.W tglO = BitVec.ofNat 32 (a.count-i)
  off : slotv u.mem a.W xlO = BitVec.ofNat 32 (a.off s.mem i)
  frame : Frame (a.frame (a.off s.mem i)) s.mem u.mem
  ctr : CtrS u.mem a.st (ciphOf s.mem a.C a.rounds) icb (a.off s.mem i)
  out : bytesAt u.mem (w64 a.O) (a.off s.mem i) = xorKs (ciphOf s.mem a.C a.rounds) icb 0 (a.buf s.mem i)

namespace TextInput

variable {a : Text} {s : State} (p : TextInput a s)
include p

theorem off_le {i : Nat} (hi : i≤a.count) : a.off s.mem i ≤ a.len := by
  rw [←p.total]
  exact Gather.gl_mono s.mem a.Src p.descFit hi (Nat.le_refl _)

theorem span {i : Nat} (hi : i<a.count) : a.off s.mem i + a.size s.mem i ≤ a.len := by
  rw [←Gather.gl_succ p.descFit hi]; exact p.off_le (by omega_using [hi])

theorem input (i : Nat) (hi : i<a.count) (pos : a.size s.mem i ≠ 0) :
    PieceRegions a.C a.W a.SP (a.source s.mem i) (atByte a.O (a.off s.mem i)) (a.size s.mem i) := by
  have span := p.span hi
  have fit := p.dstFit
  obtain nk : a.O.toNat+a.off s.mem i < 2^32 := by omega_using [span,fit,pos]
  obtain sub : Region.Sub ⟨w64 (atByte a.O (a.off s.mem i)),a.size s.mem i⟩ ⟨w64 a.O,a.len⟩ := by
    rw [w64_add nk]; exact Offset.sub_base _ span
  exact ⟨(p.srcOutside i hi).w,p.dstOutside.w.sub_left sub,p.ctxDst.sub_right sub,.inr ((p.srcDst i hi).sub_right sub),
    (p.srcOutside i hi).stack.symm,p.dstOutside.stack.symm.sub_right sub,p.argW,
    p.dstOutside.sp.symm.sub_right sub,p.spFit,p.srcFit i hi,
    by unfold atByte; rw [toNat_add32 nk]; omega_using [span,fit]⟩

theorem accesses {i : Nat} (hi : i<a.count) (pos : a.size s.mem i ≠ 0) {u : State}
    (rd : u.rd=s.rd) (wr : u.wr=s.wr) (dest : u.mem.readW (w64 a.SP) 32=atByte a.O (a.off s.mem i)) :
    PieceAccess u a.SP (a.source s.mem i) (atByte a.O (a.off s.mem i)) (a.size s.mem i) := by
  have span := p.span hi
  have fit := p.dstFit
  refine ⟨dest,by rw [rd,wr]; exact covers_left p.spW,by rw [rd,wr]; exact p.srcR i hi,?_⟩
  rw [wr,w64_add (by omega_using [fit,pos,span])]
  exact covers_off p.dstW span (by omega_using [fit])

theorem descStep {i : Nat} (hi : i<a.count) {u : State} {icb : Block} (h : TextAt a s icb i u) :
    WP isa (.block Impl.AesGcm.X86.DirectGather.nextPiece) u fun y =>
      y.mem = setup u.mem a.W a.SP (a.desc i) (a.source s.mem i) a.O (a.off s.mem i) (a.size s.mem i) ∧
      y.gpr .edi = atByte a.O (a.off s.mem i) ∧ y.zf = some (decide (a.off s.mem i%16=0)) ∧
      y.gpr .ebp=a.W ∧ y.gpr .esi=a.st ∧ y.gpr .esp=a.SP ∧ y.rd=u.rd ∧ y.wr=u.wr := by
  have od := p.off_le (Nat.le_of_lt hi)
  have du := p.descOutside.frame p.lay (p.descDst.sub_right (Region.sub_prefix od))
  have ar := p.argOutside.frame p.lay (p.argDst.sub_right (Region.sub_prefix od))
  have m0 : (⟨w64 a.Src,a.count*8⟩ : Region).Contains (w64 (a.desc i)) 4 := by
    rw [←Gather.descA0 p.descFit hi]; exact Offset.contains_base _ (by omega_using [hi]) (by have f:=p.descFit; omega_using [f,hi])
  have m4 : (⟨w64 a.Src,a.count*8⟩ : Region).Contains (w64 (a.desc i+4#32)) 4 := by
    rw [←Gather.descA p.descFit hi 4 (by decide),BitVec.add_assoc,←BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega_using [hi]) (by have f:=p.descFit; omega_using [f,hi])
  have mask := and15 (BitVec.ofNat 32 (a.off s.mem i))
  rw [toNat_ofNat32 (by have lt:=p.lenLt; omega_using [od,lt])] at mask
  have z : ((BitVec.ofNat 32 (a.off s.mem i) &&& 15#32) == 0) = decide (a.off s.mem i%16=0) := by
    rw [mask]
    simpa only [BitVec.sub_zero,Nat.reduceSub] using sub_beq32 (a:=a.off s.mem i%16) (b:=0) (by omega_using []) (by decide)
  refine WP.mono (nextPiece_ok p.lay h.env h.ptr (h.frame.readW m0 du (by decide))
    ((h.frame.readW m4 du (by decide)).trans (ofNat_toNat32 _).symm)
    (by rw [h.rd,h.wr]; exact p.descR _ _ ⟨_,List.mem_singleton_self _,m0⟩)
    (by rw [h.rd,h.wr]; exact p.descR _ _ ⟨_,List.mem_singleton_self _,m4⟩)
    (p.descOutside.w.sep m4 (Offset.contains_base _ (by decide) (by decide))) h.off
    (by rw [h.rd,h.wr]; exact p.argR)
    ((h.frame.readW (r:=⟨a.dstArg,4⟩) (Region.contains_self _ _) ar (by decide)).trans p.arg)
    (by rw [h.wr]; exact p.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩) p.argOutside.w) ?_
  rintro y ⟨m,di,hz,r,rd,wr⟩
  exact ⟨m,di,hz.trans (congrArg some z),(r .ebp (by decide) (by decide) (by decide) (by decide)).trans h.env.ebp,
    (r .esi (by decide) (by decide) (by decide) (by decide)).trans h.env.esi,
    (r .esp (by decide) (by decide) (by decide) (by decide)).trans h.env.esp,rd,wr⟩

end TextInput

end VG.Proof.AesGcm.X86.DirectGather

end
