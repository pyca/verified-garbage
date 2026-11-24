module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumStart
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.ScratchGather

/-! Permissions, padded inputs, and memory agreement for the bounded CTR-call leaf. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid
open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros padLen)
open VG.WriteBytes
open VG.Impl.AesGcm.AArch64.DirectGather

abbrev size : Fin 753 := ⟨Medium.work,by decide⟩
abbrev base (s : State) := s.sp - BitVec.ofNat 64 Medium.work
abbrev scratch (s : State) : Region := ⟨base s,Medium.work⟩
abbrev LocalMem := Compact.LocalMem size
abbrev scratch_sub := Compact.scratch_sub size
abbrev scratchArg := Compact.scratchArg size
abbrev textOff (s : State) := Medium.authO+240-16*blocks s

structure Cursors (s t : State) : Prop where
  d : t.gpr .x2 = Dst s
  auth : t.gpr .x3 = base s + BitVec.ofNat 64 (textOff s)
  key : t.gpr .x1 = base s + 240
  ds : t.gpr .x6 = Src s
  n : t.gpr .x7 = s.gpr .x7

theorem loopPre {s t : State} {extra : List Region} (l : BoundedLay s extra) (h : LocalMem s t) (p : Cursors s t)
    (hn : L s ≤ 224) : Fragment.LoopPre t := by
  apply Compact.loopPre (ko := 240) (ao := textOff s) l h p.d p.auth p.key p.ds p.n
  · change 240 + L s ≤ 720-16*((L s+15)/16); omega
  · change 720-16*((L s+15)/16)+L s ≤ 752; omega

abbrev ghBase (s : State) := base s + BitVec.ofNat 64 Medium.authO
abbrev aadOff (s : State) := Medium.authO+224-16*blocks s

structure Header (s t : State) : Prop extends LocalMem s t where
  sp : t.sp = base s
  saved : SavedAt t.mem (base s) s
  x19 : t.gpr .x19 = base s
  x21 : t.gpr .x21 = K s
  x22 : t.gpr .x22 = s.gpr .x1
  x23 : t.gpr .x23 = Nn s
  x24 : t.gpr .x24 = BitVec.ofNat 64 (AL s)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (16*blocks s)
  x26 : t.gpr .x26 = BitVec.ofNat 64 (L s)
  x6 : t.gpr .x6 = Src s
  x7 : t.gpr .x7 = s.gpr .x7

theorem entered {s : State} {extra : List Region} (l : BoundedLay s extra) (hn : L s ≤ 224) :
    WP isa (.block Medium.setup) (allocated Medium.work s) fun t => Header s t ∧ t.gpr .x4 = Ad s := by
  let a := allocated Medium.work s
  have localA : LocalMem s a := ⟨Frame.refl _ _,rfl,rfl⟩
  refine WP.mono (setup_ok a hn localA.scratchWr (localA.argRead l 1 (by decide))
    (by simpa only [a,allocated,base,Nat.mul_one,L,BitVec.ofNat_toNat,BitVec.setWidth_eq] using localA.arg l 1 (by decide))) ?_
  intro t ⟨b,k,r,n,al,len,ceil,other,saved,fr,sp,rd,wr⟩
  have localT : LocalMem s t := ⟨fr.sub (fun q hq => by
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_singleton_self _, Offset.sub_base (base s) (by decide)⟩),rd,wr⟩
  exact ⟨⟨localT,sp,saved,b,k,r,n,(by simpa only [a,allocated,AL,BitVec.ofNat_toNat,BitVec.setWidth_eq] using al),ceil,len,other _ (by decide),other _ (by decide)⟩,
    other _ (by decide)⟩

theorem aadInput {s : State} (hn : L s ≤ 224) :
    aadOff s = Medium.authO + (224-16*blocks s) := by
  unfold aadOff Medium.authO blocks
  omega

/-- The zeroed input after filling the AAD slot. The following bytes form
the padded ciphertext slot, and the last 16 bytes will hold the lengths. -/
theorem zeroAad_layout {s : State} {m : Mem} (hn : L s ≤ 224) (hal : AL s ≤ 16)
    (hz : bytesAt m (ghBase s) 256 = zeros 256) :
    bytesAt (writeBytes m (base s + BitVec.ofNat 64 (aadOff s)) (aadBytes s)) (ghBase s) 256 =
      zeros (16*(14-blocks s)) ++ aadBytes s ++ zeros (16-AL s) ++ zeros (16*blocks s) ++ zeros 16 := by
  have bound : blocks s ≤ 14 := by unfold blocks; omega
  have al : (aadBytes s).length = AL s := Proof.AesCcm.length_bytesAt _ _ _
  rw [aadInput hn,← Offset.add_add,show 224-16*blocks s = 16*(14-blocks s) by omega]
  simpa only [al] using paddedAad (G := ghBase s) (k := 14) (b := blocks s)
    (aadBytes s) bound (by rw [al]; exact hal) (by decide) hz


abbrev aadLayout (s : State) := zeros (16*(14-blocks s)) ++ aadBytes s ++
  zeros (16-AL s) ++ zeros (16*blocks s) ++ zeros 16

theorem Header.advance {s t u : State} (h : Header s t) {d n : Nat}
    (f : Frame [⟨base s + BitVec.ofNat 64 d,n⟩] t.mem u.mem)
    (low : 216 ≤ d) (high : d+n ≤ Medium.work)
    (g : ∀ r, r ∉ loopRegs → u.gpr r = t.gpr r) (sp : u.sp = t.sp)
    (rd : u.rd = t.rd) (wr : u.wr = t.wr) : Header s u := by
  have subF : Frame [scratch s] t.mem u.mem := f.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ high⟩
  refine ⟨⟨h.frame.trans subF,rd.trans h.rd,wr.trans h.wr⟩,sp.trans h.sp,h.saved.frame f ?_,
    (g _ (by decide)).trans h.x19,(g _ (by decide)).trans h.x21,(g _ (by decide)).trans h.x22,
    (g _ (by decide)).trans h.x23,(g _ (by decide)).trans h.x24,(g _ (by decide)).trans h.x25,
    (g _ (by decide)).trans h.x26,(g _ (by decide)).trans h.x6,(g _ (by decide)).trans h.x7⟩
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint _ (.inl low) (by decide) (by change d+n ≤ 752 at high; omega)

/-- After setup and AAD absorption, only the short frame has changed. -/
theorem prefix_ok {s : State} {extra : List Region} (l : BoundedLay s extra) (hn : L s ≤ 224) (hal : AL s ≤ 16) :
    WP isa (.seq (.block Medium.setup) (.seq (.block Medium.zero) Medium.aad)) (allocated Medium.work s)
      fun t => Header s t ∧ bytesAt t.mem (ghBase s) 256 = aadLayout s ∧
        bytesAt t.mem (base s+224) 256 = zeros 256 ∧ bytesAt t.mem (base s+736) 16 = zeros 16 := by
  refine WP.seq ((entered l hn).mono ?_)
  intro a ⟨ha,a4⟩
  refine WP.seq ((zero_ok a ha.x19 ha.scratchWr).mono ?_)
  intro z ⟨zm,zg,zsp,zrd,zwr⟩
  have fz : Frame [⟨base s+224,528⟩] a.mem z.mem := by
    rw [zm]; apply writeBytes_frame
    rw [List.length_replicate]; exact Region.contains_self _ _
  have hz := ha.advance fz (by decide) (by decide) (fun r _ => congrFun zg r) zsp zrd zwr
  have zfull : bytesAt z.mem (base s+224) 528 = zeros 528 := by
    rw [zm,show BitVec.ofNat 64 Medium.keyO = (224:Addr) by decide]; simpa only [zeros,List.length_replicate] using bytesAt_writeBytes_self a.mem (base s+224) (List.replicate 528 0) (by rw [List.length_replicate]; decide)
  have slice (i n : Nat) (h : i+n ≤ 528) : bytesAt z.mem (base s+224+BitVec.ofNat 64 i) n = zeros n := by
    rw [Proof.Cmac.Stream.bytesAt_offset _ _ h,zfull]
    simp only [zeros,List.drop_replicate,List.take_replicate]
    rw [Nat.min_eq_left (by omega)]
  have z0 : bytesAt z.mem (ghBase s) 256 = zeros 256 := by
    simpa only [ghBase,Medium.authO,BitVec.add_assoc,show (224:Addr)+256#64=480#64 by decide] using slice 256 256 (by decide)
  have z4 := (congrFun zg .x4).trans a4
  have al : (aadBytes s).length = AL s := Proof.AesCcm.length_bytesAt _ _ _
  have ar : aR s ∈ s.rd := by rw [l.rd]; simp
  have b6 : blocks s ≤ 14 := by unfold blocks; omega
  have asub : (⟨base s + BitVec.ofNat 64 (aadOff s), AL s⟩ : Region).Sub (scratch s) :=
    Offset.sub_base _ (by change 480+224-16*blocks s+AL s ≤ 752; omega)
  have ad : bytesAt z.mem (z.gpr .x4) (AL s) = aadBytes s := by
    rw [z4]; exact bytesAt_frame hz.frame (by simpa only [List.mem_singleton,forall_eq] using
      (l.ba.sub_left (scratch_sub s)).symm) (by omega)
  refine (aad_ok b6 z hz.x19 hz.x25 hz.x24 ?_).mono ?_
  · rw [z4]
    exact ⟨by omega,Covers.of_mem (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      rw [hz.rd]; exact List.mem_append_left _ ar),
      covers_off hz.scratchWr (by change 480+224-16*blocks s+AL s ≤ 752; omega) (by decide),
      ((l.ba.sub_left (scratch_sub s)).sub_left asub).symm⟩
  · intro t ⟨tm,tg,tsp,trd,twr⟩
    rw [ad] at tm
    have f : Frame [⟨base s+BitVec.ofNat 64 (aadOff s),AL s⟩] z.mem t.mem := by
      rw [tm]; apply writeBytes_frame
      rw [al]; exact Region.contains_self _ _
    refine ⟨hz.advance f (by change 216 ≤ 480+224-16*blocks s; omega)
      (by change 480+224-16*blocks s+AL s ≤ 752; omega) tg tsp trd twr,?_,?_,?_⟩
    · rw [tm]; exact zeroAad_layout hn hal z0
    · rw [bytesAt_frame f (by
        intro q hq; obtain rfl := List.mem_singleton.mp hq
        exact Offset.disjoint _ (.inl (by change 224+256 ≤ 480+224-16*blocks s; omega))
          (by decide) (by change 480+224-16*blocks s+AL s ≤ 2^64; omega)) (by decide)]
      simpa only [BitVec.add_zero] using slice 0 256 (by decide)
    · rw [bytesAt_frame f (by
        intro q hq; obtain rfl := List.mem_singleton.mp hq
        exact Offset.disjoint _ (.inr (by change 480+224-16*blocks s+AL s ≤ 736; omega))
          (by decide) (by change 480+224-16*blocks s+AL s ≤ 2^64; omega)) (by decide)]
      simpa only [BitVec.add_assoc,show (224:Addr)+512#64=736 by decide] using slice 512 16 (by decide)

theorem authFilled {s : State} {m m' : Mem} {extra : List Region} (l : BoundedLay s extra)
    (hn : L s ≤ 224) (hal : AL s ≤ 16) (ct : List Byte) (hlen : ct.length = L s)
    (f : Frame [dR s,⟨base s + BitVec.ofNat 64 (textOff s),L s⟩] m m')
    (b : bytesAt m (ghBase s) 256 = aadLayout s)
    (v : bytesAt m' (base s + BitVec.ofNat 64 (textOff s)) (L s) = ct) :
    bytesAt m' (ghBase s) 240 = zeros (16*(14-blocks s)) ++ aadBytes s ++ zeros (16-AL s) ++ ct ++
      zeros (padLen (L s)) := by
  let pre := zeros (16*(14-blocks s)) ++ aadBytes s ++ zeros (16-AL s)
  have ha := Proof.AesCcm.length_bytesAt s.mem (Ad s) (AL s)
  change (aadBytes s).length = AL s at ha
  have hc : blocks s ≤ 14 := by unfold blocks; omega
  have hp : pre.length = 240-16*blocks s := by simp [pre,zeros,ha]; omega
  have pad : L s + padLen (L s) = 16 * blocks s := by unfold padLen blocks; omega
  have u := fillSlot (width := 240) (by decide) (m := m) (m' := m') (G := ghBase s) (dst := dR s)
    pre (zeros (padLen (L s))) ct
  have pos : ghBase s + BitVec.ofNat 64 pre.length = base s + BitVec.ofNat 64 (textOff s) := by
    rw [hp,ghBase,Offset.add_add]
    congr 2
    unfold textOff Medium.authO; omega
  apply u
  · simpa only [pos,hlen] using f
  · exact (l.bd.sub_left (scratch_sub s)).sub_left (Offset.sub_base _ (by decide))
  · simp [hp,hlen,zeros]; omega
  · rw [Proof.AesCcm.bytesAt_prefix _ _ (show 240 ≤ 256 by decide),b]
    have eq : aadLayout s = (pre ++ zeros ct.length ++ zeros (padLen (L s))) ++ zeros 16 := by
      change (pre ++ zeros (16*blocks s)) ++ zeros 16 = _
      rw [List.append_assoc pre (zeros ct.length),show zeros ct.length ++ zeros (padLen (L s)) = zeros (16*blocks s) by
        rw [zeros,zeros,zeros,List.replicate_append_replicate,hlen,pad]]
    rw [eq,List.take_left']
    simp [hp,zeros,hlen]; omega
  · simpa only [pos,hlen] using v


end VG.Proof.AesGcm.AArch64.DirectGather.Mid
