module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Round
import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Aes

/-! # Load and store a single SM4 block in big-endian word order -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4.AArch64.Serial

theorem wordReg_ne_base : ∀ j < 4, wordReg j ≠ .x5 := by decide

theorem readBE_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    rev32 (m.readW (p + BitVec.ofNat 64 (4*i)) 32) =
      Spec.Sm4.wordAt (Spec.Sm4.blockAt m p) (4*i) := by
  rw [rev32_readW,Spec.Sm4.wordAt]
  rw [VG.Proof.Sm4.blockAt_getD _ _ (by omega),VG.Proof.Sm4.blockAt_getD _ _ (by omega),
    VG.Proof.Sm4.blockAt_getD _ _ (by omega),VG.Proof.Sm4.blockAt_getD _ _ (by omega)]
  have add1 (j : Nat) : p + BitVec.ofNat 64 (j+1) = p + BitVec.ofNat 64 j + 1 := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
  simp only [show 4*i+2 = (4*i+1)+1 by omega,
    show 4*i+3 = ((4*i+1)+1)+1 by omega,add1]

theorem loadWord_run {s : State} {r : Reg} {i : Nat} (hi : i < 4)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.ldr .w r .x5 (768+4*i),.rev32 r r] s = some t ∧
      (t.gpr r).setWidth 32 = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 32)
  let b := a.write .w r (rev32 (a.read .w r))
  refine ⟨b,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_ldr_w ⟨by omega,by omega⟩ hread,runStep_some,
      runBlock_cons,exec_rev32,runStep_some,runBlock_nil]
  · simp only [b,a,gpr_write_self,State.read,Size.bits,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    simp only [b,a,gpr_write_of_ne _ _ _ hq]

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.ldr .w (wordReg i) .x5 (768+4*i),.rev32 (wordReg i) (wordReg i)]) s = some t ∧
      (∀ j < n, words t j = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32)) ∧
      (∀ r, (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega),fun _ _ => rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,am,ard,awr,asp,avec⟩ := ih (by omega)
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base j (by omega)).symm)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [ard,awr,ab]
      exact hread n (by omega)
    obtain ⟨b,be,bv,bg,bm,brd,bwr,bsp,bvec⟩ := loadWord_run (r := wordReg n) (by omega) ar
    refine ⟨b,?_,?_,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        simpa only [words,am,ab] using bv
      · rw [words,bg _ (fun e => h (wordReg_inj _ (by omega) _ (by omega) e))]
        exact aw j (by omega)
    · intro r hr
      exact (bg r (hr n (by omega))).trans (ag r (fun j hj => hr j (by omega)))

theorem storeWord_run {s : State} {r : Reg} {i : Nat} (hr : r ≠ .x5) (hi : i < 4)
    (hwrite : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa [.rev32 r r,.str .w r .x5 (768+4*i)] s = some t ∧
      t.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) (rev32 ((s.gpr r).setWidth 32)) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (rev32 ((s.gpr r).setWidth 32))
  let t := { a with mem := a.mem.writeW (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) ((a.gpr r).setWidth 32) }
  have base : a.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ hr.symm
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [runBlock_cons,exec_rev32,runStep_some,runBlock_cons]
    rw [exec_str_w ⟨by omega,by omega⟩ (by
      change InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4
      rw [base]; exact hwrite),runStep_some,runBlock_nil]
    rfl
  · simp only [t,a,base,gpr_write_self,mem_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]
  · intro q hq
    exact gpr_write_of_ne _ _ _ hq

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) :
    Frame [⟨p,4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW,Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

theorem stores_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hwrite : ∀ i < 4, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (768+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.rev32 (wordReg (3-i)) (wordReg (3-i)),.str .w (wordReg (3-i)) .x5 (768+4*i)]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (768+4*j)) 32 = rev32 (words s (3-j))) ∧
      (∀ r, (∀ j < n, r ≠ wordReg (3-j)) → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ h => absurd h (by omega),fun _ _ => rfl,Frame.refl _ _,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ag,af,ard,awr,asp,avec⟩ := ih (by omega)
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne_base (3-j) (by omega)).symm)
    have av : a.gpr (wordReg (3-n)) = s.gpr (wordReg (3-n)) := ag _ (fun j hj he => by
      have := wordReg_inj (3-n) (by omega) (3-j) (by omega) he
      omega)
    have ar : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (768+4*n)) 4 := by
      rw [awr,ab]
      exact hwrite n (by omega)
    obtain ⟨b,be,bm,bg,brd,bwr,bsp,bvec⟩ := storeWord_run (wordReg_ne_base (3-n) (by omega)) (by omega) ar
    have bmem : b.mem = a.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (768+4*n)) (rev32 (words s (3-n))) := by
      simpa only [ab,av,words] using bm
    have bf : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 (768+4*n),4⟩] a.mem b.mem := by
      rw [bmem]
      exact frame_write_word _ _ _
    refine ⟨b,?_,?_,?_,?_,brd.trans ard,bwr.trans awr,bsp.trans asp,bvec.trans avec⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro j hj
      by_cases h : j = n
      · subst j
        rw [bmem,Mem.readW_writeW_self32]
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr .x5) (by omega) (by omega) (by omega)) (by decide)]
        exact aw j (by omega)
    · intro r hr
      exact (bg r (hr n (by omega))).trans (ag r (fun j hj => hr j (by omega)))
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_,List.mem_cons_self,?_⟩
      rw [← VG.Offset.add_add (s.gpr .x5) 768 (4*n)]
      exact VG.Offset.sub_base _ (by omega : 4*n+4 ≤ 16)

theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4*i)) 32 = rev32 (z (3-i))) :
    Spec.Aes.bytesAt m p 16 = (VG.Proof.Sm4.outBlock z).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi hi'
  have hi16 : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
  simp only [Spec.Aes.bytesAt,List.getElem_map,List.getElem_range,Vector.getElem_toList]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p+BitVec.ofNat 64 (4*(i/4))) (i := i%4) (by omega)
  rw [VG.Offset.add_add,show 4*(i/4)+i%4 = i by omega,h (i/4) (by omega)] at b
  rw [b,BitVec.getLsbD_extractLsb',VG.Proof.Sm4.getLsbD_outBlock' z hi16 hj]
  simp only [hj,decide_true,Bool.true_and]
  change (byteRev32 (z (3-i/4))).getLsbD (8*(i%4)+j) = _
  rw [byteRev32_getLsbD _ (by omega)]
  congr 1 <;> omega

end VG.Proof.Sm4.AArch64.Serial
