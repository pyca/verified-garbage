module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Chunk

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Spill

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

variable {sve : Bool}

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 512 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S (8 * t)) ((k - 512 * t) / 64)))).getD
        ((k - 512 * t) % 64) 0 := by
  rw [keystream_getD _ hk,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show 8 * t + (k - 512 * t) / 64 = k / 64 by omega_arith,
    show (k - 512 * t) % 64 = k % 64 by omega_arith]

 theorem next_ok (s : State) (hlen : 512 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 512 ∧ u.gpr .x2 = s.gpr .x2 - 512 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 512 < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 8 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, next,VG.Impl.ChaCha20.AArch64.Mixed5.counter,check,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 512 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 512) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega_arith
    rw [he,less8 _ (by have h := (s.gpr .x2).isLt; omega_arith)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) 8
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

 theorem zero_batches {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (512 ≤ n)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x5,h]
  by_cases hn : n < 512
  · simp only [ite_eq_left hn]
    have hnn : ¬ 512 ≤ n := by omega_arith
    simp [hnn]
  · simp only [ite_eq_right hn]
    have hnn : 512 ≤ n := by omega_arith
    simp [hnn]

/-! ## `vg_chacha20_xor`'s chunks

`Mixed8.xor` keeps the source in `x27` and the destination in `x1`
(`enterFrom`), and our caller's registers saved at `x3 + 256` (`savedFrom`)
and `x3 + 128`, relative to the entry state `s₀` (`Xor.TPre`). -/

open VG.Proof.ChaCha20.AArch64.Xor (TPre tp tR T0 Dst Src)

/-- Our caller's `x20`, `x19`, `x26` and `x27`, saved at `buf + 256`. -/
abbrev TSaved (s₀ : State) (m : Mem) : Prop := Spill.Saved (bp s₀) s₀.gpr savedFrom m

/-- Before chunk `t` of `vg_chacha20_xor`. -/
structure TInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = tp s₀ + BitVec.ofNat 64 (512 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t)
  x3 : s.gpr .x3 = bp s₀
  x20 : s.gpr .x20 = bp s₀
  x27 : s.gpr .x27 = dp s₀ + BitVec.ofNat 64 (512 * t)
  le : 512 * t ≤ L s₀
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x27 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (8 * t)
  data : Dst s₀ (512 * t) s.mem
  src : Src s₀ (512 * t) s.mem
  saved : TSaved s₀ s.mem
  savedV : ∀ j : Fin 2, s.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
    s₀.v (#[VReg.v8,VReg.v9][j])

/-- The destination's window of chunk `t`, and the source's. -/
abbrev twin (s₀ : State) (t : Nat) : Region := ⟨tp s₀ + BitVec.ofNat 64 (512 * t),512⟩
abbrev swin (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (512 * t),512⟩

theorem twin_sub {s₀ : State} {t : Nat} (h : 512 * t + 512 ≤ L s₀) :
    Region.Sub (twin s₀ t) (tR s₀) := Offset.sub_base _ h
theorem swin_sub {s₀ : State} {t : Nat} (h : 512 * t + 512 ≤ L s₀) :
    Region.Sub (swin s₀ t) (dR s₀) := Offset.sub_base _ h

/-- The chunk's precondition, and its source's. -/
theorem tcp_of_inv {s₀ s : State} (hp : TPre s₀) {t : Nat} (h : TInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) : CP s ∧ SrcOK .x27 s := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hw : s.wr = [stR s₀,tR s₀,bR s₀] := h.wr.trans hp.wr
  have hr : s.rd = [dR s₀] := h.rd.trans hp.rd
  refine ⟨⟨h.x20.trans h.x3.symm,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨.inr rfl,?_,?_,?_,?_⟩⟩
  · intro k; rw [hr,hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · intro k; rw [hr,hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  · intro d n hn; rw [hw,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hn (by omega_arith)⟩
  · intro d n hn; rw [hw,h.x1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨tR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x0,h.x3]; exact hp.st_b
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x0,h.x1]; exact hp.st_t.sub_right (twin_sub hge)
  · change (⟨s.gpr .x1,512⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x1,h.x3]; exact hp.t_b.sub_left (twin_sub hge)
  · intro d n hn; rw [hr,hw,h.x27,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x27,512⟩
    rw [h.x0,h.x27]; exact hp.st_d.sub_right (swin_sub hge)
  · change (⟨s.gpr .x27,512⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x27,h.x3]; exact hp.d_b.sub_left (swin_sub hge)
  · change s.gpr .x27 = s.gpr .x1 ∨ (⟨s.gpr .x27,512⟩ : Region).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x27,h.x1]
    rcases hp.alias with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left (swin_sub hge)).sub_right (twin_sub hge))

/-- The destination after a chunk. -/
theorem tchunkData {s₀ s u : State} (hp : TPre s₀) {t : Nat} (h : TInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) (hu : ChunkedFrom .x27 s u) : Dst s₀ (512 * (t + 1)) u.mem := by
  intro k hk
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  by_cases hin : 512 * t ≤ k ∧ k < 512 * t + 512
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 512 * t) = tp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1,BitVec.add_assoc,← BitVec.ofNat_add,Nat.add_sub_cancel' hin.1]
    have hs : s.gpr .x27 + BitVec.ofNat 64 (k - 512 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x27,BitVec.add_assoc,← BitVec.ofNat_add,Nat.add_sub_cancel' hin.1]
    have hh := hu.data (k - 512 * t) (by omega_arith)
    rw [he,hs,h.src k hk hin.1,source,h.x0,h.cnt, ← ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega_arith)]; exact hh
  · have hct : (tR s₀).Contains (tp s₀ + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    have hx : ¬ (twin s₀ t).Contains (tp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains,Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega_arith),Mem.sub_ofNat_toNat _ (by omega_arith : k < 2 ^ 64)]
      exact hin
    have hh := hu.frame (tp s₀ + BitVec.ofNat 64 k) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change ¬ (⟨s.gpr .x0,64⟩ : Region).Contains _ 1
        rw [h.x0]; exact fun hc => hp.st_t _ hc hct
      · exact fun hc => hp.t_b _ hct
          (Region.sub_prefix (by decide : 128 ≤ 320) _ (by simpa only [scalarBuf,h.x3] using hc))
      · change ¬ (⟨s.gpr .x1,512⟩ : Region).Contains _ 1
        rw [h.x1]; exact hx)
    rw [hh,h.data k hk]
    by_cases hold : k < 512 * t
    · rw [ite_eq_left hold,ite_eq_left (by omega_arith)]
    · rw [ite_eq_right hold,ite_eq_right (by omega_arith)]

/-- Our caller's registers, saved at `buf[128, 160)` and `buf[256, 288)`, are
apart from what a chunk writes. -/
theorem tsaved_chunk {s₀ s : State} (hp : TPre s₀) {t : Nat} (h : TInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) {d n : Nat} (hd : 128 ≤ d) (hn : d + n ≤ 320) :
    ∀ r ∈ [sr s,scalarBuf s,dr s], (⟨bp s₀ + BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨bp s₀ + BitVec.ofNat 64 d,n⟩ (bR s₀) := Offset.sub_base _ hn
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (⟨bp s₀ + BitVec.ofNat 64 d,n⟩ : Region).Disjoint ⟨s.gpr .x0,64⟩
    rw [h.x0]; exact hp.st_b.symm.sub_left hsub
  · change (⟨bp s₀ + BitVec.ofNat 64 d,n⟩ : Region).Disjoint ⟨s.gpr .x3,128⟩
    rw [h.x3]; exact Offset.disjoint_base _ hd (by omega_arith)
  · change (⟨bp s₀ + BitVec.ofNat 64 d,n⟩ : Region).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x1]; exact (hp.t_b.symm.sub_left hsub).sub_right (twin_sub hge)

/-- After a chunk from the source at `x27` (any code that leaves what
`chunkFrom` does: ChaCha20-Poly1305's stitched chunks too), the counter and
the pointers advanced. -/
theorem tnext_ok {s₀ : State} (hp : TPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s u : State} (h : TInv s₀ t s) (hu : ChunkedFrom .x27 s u) :
    WP isa (.block (next ++ ([.addImm .x .x27 .x27 512] : List Instr))) u fun v => TInv s₀ (t + 1) v ∧
      v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0) ∧
      Frame [stR s₀] u.mem v.mem := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = tp s₀ + BitVec.ofNat 64 (512 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hx27 : u.gpr .x27 = dp s₀ + BitVec.ofNat 64 (512 * t) :=
    (hu.cs _ (by simp [preserved]) (by decide) (by decide)).trans h.x27
  have hx20 : u.gpr .x20 = bp s₀ :=
    (hu.cs _ (by simp [preserved]) (by decide) (by decide)).trans h.x20
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (8 * t) := by
    have hc := hu.cnt
    change stateAt u.mem (u.gpr .x0) = stateAt s.mem (s.gpr .x0) at hc
    rw [hx0,h.x0,h.cnt] at hc
    exact hc
  have hdata := tchunkData hp h hge hu
  have hsrc' : Src s₀ (512 * (t + 1)) u.mem :=
    VG.Proof.ChaCha20.AArch64.Xor.src_step' hp (by omega_arith) h.src hu.frame (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · left; change (dR s₀).Disjoint ⟨s.gpr .x0,64⟩; rw [h.x0]; exact hp.st_d.symm
      · left; change (dR s₀).Disjoint ⟨s.gpr .x3,128⟩; rw [h.x3]
        exact hp.d_b.sub_right (Region.sub_prefix (by decide : 128 ≤ 320))
      · right; change Region.Sub ⟨s.gpr .x1,512⟩ (tR s₀); rw [h.x1]; exact twin_sub hge) hdata
  have hw : u.wr = [stR s₀,tR s₀,bR s₀] := hu.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hu.rd,h.rd,hp.rd,hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 512 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith)]
  have hsaved : TSaved s₀ u.mem :=
    Spill.Saved.frame_in h.saved (lo := 256) (n := 32) (by decide) hu.frame
      (tsaved_chunk hp h hge (by decide) (by decide))
  have hsavedV : ∀ j : Fin 2, u.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
      s₀.v (#[VReg.v8,VReg.v9][j]) := by
    intro j
    rw [hu.frame.read (r := ⟨bp s₀ + BitVec.ofNat 64 128,32⟩)
      (Offset.contains (bp s₀) (by omega) (by have := j.isLt; omega) (by decide))
      (tsaved_chunk hp h hge (by decide) (by decide)) (by decide),h.savedV j]
  apply WP.block_append
  refine (next_ok u (by rw [hlen]; omega_arith) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ?_
  have hns : ∀ r ∈ [⟨u.gpr .x0,64⟩], (⟨bp s₀ + BitVec.ofNat 64 128,32⟩ : Region).Disjoint r ∧
      (⟨bp s₀ + BitVec.ofNat 64 256,32⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [hx0]
    exact ⟨hp.st_b.symm.sub_left (Offset.sub_base _ (by decide)),
      hp.st_b.symm.sub_left (Offset.sub_base _ (by decide))⟩
  refine VG.Proof.ChaCha20.AArch64.Xor.WP.cons
    (s' := v.write .x .x27 (v.gpr .x27 + BitVec.ofNat 64 512)) (by simp [exec, State.read])
    (WP.block_nil ?_)
  have g : ∀ r, r ≠ .x27 → (v.write .x .x27 (v.gpr .x27 + BitVec.ofNat 64 512)).gpr r = v.gpr r :=
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr
  have hadv : ∀ p : Addr, p + BitVec.ofNat 64 (512 * t) + 512 = p + BitVec.ofNat 64 (512 * (t + 1)) := by
    intro p
    rw [BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 512) = _
    rw [← BitVec.ofNat_add,show 512 * t + 512 = 512 * (t + 1) by omega_arith]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,by omega_arith,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_,?_,?_⟩,?_,
    by simpa only [stR, hx0, RegUpd.mem_write] using hframe⟩
  · rw [g _ (by decide),hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [g _ (by decide),hv1,hx1,hadv]
  · rw [g _ (by decide),hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 512 * t) - BitVec.ofNat 64 512 = _
    rw [Offset.ofNat_sub_ofNat (by omega_arith),show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega_arith]
  · rw [g _ (by decide),hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · rw [g _ (by decide),hkeep _ (by decide) (by decide) (by decide) (by decide),hx20]
  · rw [RegUpd.gpr_write_self,BitVec.setWidth_eq,hkeep _ (by decide) (by decide) (by decide) (by decide),
      hx27]
    exact hadv _
  · intro r hr h19 h20 h21 h26
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [g r h21,hkeep r n1 n2 n4 n5,hu.cs r hr h19 h26,h.cs r hr h19 h20 h21 h26]
  · show stateAt v.mem (st s₀) = _
    rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega_arith] at hctr
    exact hctr
  · show Dst s₀ (512 * (t + 1)) v.mem
    refine hdata.frame hframe ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [hx0]; exact hp.st_t.symm
  · show Src s₀ (512 * (t + 1)) v.mem
    refine hsrc'.frame hframe ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [hx0]; exact hp.st_d.symm
  · show TSaved s₀ v.mem
    exact Spill.Saved.frame_in hsaved (lo := 256) (n := 32) (by decide) hframe (fun r hr => (hns r hr).2)
  · intro j
    show v.mem.read _ 16 = _
    rw [hframe.read (r := ⟨bp s₀ + BitVec.ofNat 64 128,32⟩)
      (Offset.contains (bp s₀) (by omega) (by have := j.isLt; omega) (by decide))
      (fun r hr => (hns r hr).1) (by decide),hsavedV j]
  · rw [g _ (by decide),hv5,hlen,show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega_arith]

theorem tbody_ok {s₀ : State} (hp : TPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : TInv s₀ t s) :
    WP isa (bodyFrom sve) s fun u => TInv s₀ (t + 1) u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0) := by
  obtain ⟨hcp,hsrc⟩ := tcp_of_inv hp h hge
  exact WP.seq ((chunkFrom_ok .x27 s hcp hsrc).mono fun _ hu =>
    (tnext_ok hp hge h hu).mono fun _ ⟨hi, h5, _⟩ => ⟨hi, h5⟩)

theorem tbulk_ok {s₀ : State} (hp : TPre s₀) {s : State} (h : TInv s₀ 0 s)
    (hge : 512 ≤ L s₀) : WP isa (.loop (bodyFrom sve) (.zero .x .x5)) s fun u =>
      ∃ t, L s₀ - 512 * t < 512 ∧ TInv s₀ t u := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ t, n = L s₀ - 512 * t ∧ 512 ≤ n ∧ TInv s₀ t s
  refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega_arith,hge,h⟩
  intro n s ⟨t,hn,hge,hi⟩
  refine (tbody_ok hp (by omega_arith) hi).mono fun u ⟨hu,h5⟩ => ?_
  have hc := zero_batches h5
  by_cases he : L s₀ - 512 * (t + 1) < 512
  · left
    refine ⟨?_,t + 1,he,hu⟩
    have hne : ¬ 512 ≤ L s₀ - 512 * (t + 1) := by omega_arith
    simpa only [decide_eq_false hne] using hc
  · right
    refine ⟨?_,L s₀ - 512 * (t + 1),by omega_arith,t + 1,rfl,by omega_arith,hu⟩
    have hne : 512 ≤ L s₀ - 512 * (t + 1) := by omega_arith
    simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Mixed8
