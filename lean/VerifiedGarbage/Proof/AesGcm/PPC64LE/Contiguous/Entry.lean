module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # Register preservation and argument setup of contiguous POWER AES-GCM seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous (entry)

structure Arguments (s : State) (w : Addr) : Prop where
  work : Covers [⟨w,1152⟩] s.wr
  scratch : s.mem.readW (s.sp + 112) 64 = w
  slot : ∀ i < 3, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (96+8*i)) 8
  apart : ∀ i < 2, (⟨s.sp + BitVec.ofNat 64 (96+8*i),8⟩ : Region).Disjoint (savedR w)

/-- Register values passed on to nonce/AAD and payload processing. -/
structure Started (s : State) (w : Addr) (t : State) : Prop where
  entered : Entered s w t
  scratch : t.gpr .r31 = w
  stream : t.gpr .r30 = w + 16
  key : t.gpr .r29 = s.gpr .r3
  rounds : t.gpr .r28 = s.gpr .r4
  nonce : t.gpr .r24 = s.gpr .r5
  nonceLen : t.gpr .r25 = s.gpr .r6
  nonceLenSaved : t.gpr .r18 = s.gpr .r6
  aad : t.gpr .r21 = s.gpr .r7
  aadLen : t.gpr .r22 = s.gpr .r8
  src : t.gpr .r19 = s.gpr .r9
  dst : t.gpr .r27 = s.gpr .r10
  len : t.gpr .r23 = s.mem.readW (s.sp+96) 64
  tag : t.gpr .r20 = s.mem.readW (s.sp+104) 64

theorem entry_wp {s : State} {w : Addr} (a : Arguments s w) : WP isa (.block entry) s (Started s w) := by
  unfold entry
  refine WP.block_append (WP.block_append ?_)
  refine WP.mono (oneA_at (off := 112) (by decide) (by decide) (a.slot 2 (by decide)) a.scratch)
    fun u ⟨hw,g,k⟩ => ?_
  refine WP.mono (save_ok (b := .r12) (n := 1152) (by decide) (by rw [hw,k.wr]; exact a.work) (by decide))
    fun v ⟨vg,vw,vk,saved,frame⟩ => ?_
  rw [hw] at vw saved frame
  have ptr (i : Nat) (hi : i < 2) : InRegions (v.rd ++ v.wr) (v.sp + BitVec.ofNat 64 (96+8*i)) 8 := by
    rw [vk.rd,vk.wr,vk.sp,k.rd,k.wr,k.sp]
    exact a.slot i (by omega)
  have val (i : Nat) (hi : i < 2) :
      v.mem.readW (v.sp + BitVec.ofNat 64 (96+8*i)) 64 =
      s.mem.readW (s.sp + BitVec.ofNat 64 (96+8*i)) 64 := by
    rw [vk.sp,k.sp,frame.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact a.apart i hi) (by decide),k.mem]
  have arg (r : Reg) (nz : r ≠ .r0) (ns : r ≠ .r12) (nw : r ≠ .r31) : v.gpr r = s.gpr r :=
    (vg r nz nw).trans (g r ns)
  have kept : Entered s w v := by
    refine ⟨fun r hr => arg r (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide), ⟨vk.rd.trans k.rd,vk.wr.trans k.wr,vk.sp.trans k.sp,vk.lr.trans k.lr⟩,
      saved.congr (fun p hp => (g p.1 (by revert hp; revert p; decide)).symm) k.lr.symm, ?_⟩
    rw [← k.mem]
    exact frame
  have rd96 := ptr 0 (by decide)
  have rd104 := ptr 1 (by decide)
  have v96 := val 0 (by decide)
  have v104 := val 1 (by decide)
  change InRegions _ (v.sp + BitVec.ofNat 64 96) 8 at rd96
  change InRegions _ (v.sp + BitVec.ofNat 64 104) 8 at rd104
  change v.mem.readW (v.sp + BitVec.ofNat 64 96) 64 = s.mem.readW (s.sp + 96) 64 at v96
  change v.mem.readW (v.sp + BitVec.ofNat 64 104) 64 = s.mem.readW (s.sp + 104) 64 at v104
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,addr,State.load,State.write,Size.bytes,
    rd96,rd104,Proof.Gcm.PPC64LE.read_8,v96,v104,mov,BitVec.or_self,vw,
    implies_true,and_self,Option.bind_some,Option.map_some,Option.some.injEq,exists_eq_left',reduceCtorEq,ne_eq,
    not_false_eq_true,Nat.reduceLT,Nat.reducePow,Nat.reduceMod,↓reduceIte,BitVec.setWidth_eq,BitVec.add_zero]
  refine ⟨⟨?_,⟨kept.keeps.rd,kept.keeps.wr,kept.keeps.sp,kept.keeps.lr⟩,kept.saved,kept.frame⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    have low := kept.low r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact low
  all_goals first | exact vw | rfl | exact arg _ (by decide) (by decide) (by decide)

end VG.Proof.AesGcm.PPC64LE.Contiguous
