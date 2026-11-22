module

public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-!
# FFDH on i686: `prepare .wide`, called

`prepCall` calls `prepare .wide` (`vg_ffdh_prepare_wide`) in a frame of its own of 76 bytes, which it
fills with a copy of the caller's synthetic arguments (`copyArg`): the operations read them at `esp`.
The call changes the 176 bytes below the caller's `esp` (its return address, the frame and the
operations' 96 bytes) and the working space's ranges of `prepare` (`prepCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Impl.Ffdh.X86

/-- The first `c` synthetic arguments copied into the frame at `P` (`esp`) from the words `g`
above it, keeping everything else but `eax`. -/
theorem copyArgs_ok {t : State} {g : Nat → BitVec 32} {P : Addr}
    (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32)
    (hfr : (⟨P, 76⟩ : Region) ∈ t.wr)
    (hr : ∀ j < 18, readSrc t (.mem (at_ .esp (84 + 4 * j))) = some (g j))
    (hargs : ∀ j < 18, Region.Disjoint ⟨t.ea (at_ .esp (84 + 4 * j)), 4⟩ ⟨P, 76⟩) :
    ∀ c, c ≤ 18 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ u, Keeps [.eax] t u → Frame [⟨P, 76⟩] t.mem u.mem →
        (∀ i < c, u.mem.readW (slotAddr P i) 32 = g i) → WP isa (.block is) u Q) →
      WP isa (.block ((List.range c).flatMap copyArg ++ is)) t Q
  | 0, _, _, _, k => k t (Keeps.refl _ _) (Frame.refl _ _) fun _ h => absurd h (by omega_using [])
  | c + 1, hc, is, Q, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine copyArgs_ok hP hesp hfr hr hargs c (by omega_using [hc]) fun u K F S => ?_
    obtain hr' : readSrc u (.mem (at_ .esp (84 + 4 * c))) = some (g c) := by
      rw [← hr c (by omega_using [hc])]
      exact src_frame K (by decide) F fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hargs c (by omega_using [hc])
    unfold copyArg
    simp only [List.cons_append, List.nil_append]
    refine wp_movS hr' fun v U _ => ?_
    obtain Kv : Keeps [.eax] u v := U.keeps
    obtain Pv : (v.gpr .esp).setWidth 64 = P := by rw [Kv.1 _ (by decide), K.1 _ (by decide), hP]
    obtain ev' : (v.gpr .esp).toNat + 76 ≤ 2 ^ 32 := by rw [Kv.1 _ (by decide), K.1 _ (by decide)]; exact hesp
    obtain wv : (⟨P, 76⟩ : Region) ∈ v.wr := by rw [Kv.2.2, K.2.2]; exact hfr
    obtain ⟨ea, wr⟩ := frame76_store Pv ev' wv (i := c) (by omega_using [hc])
    refine wp_storeS ea wr fun w M => ?_
    refine k w ((K.trans Kv).trans ((M.keeps []).mono (by decide))) ?_ fun i hi => ?_
    · rw [M.mem, U.mem]
      exact F.trans (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc])))
    · rw [M.mem, U.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [frame76_other _ _ _ (by omega_using [hi]) (by omega_using [hc]) (by omega_arith), S i hi]
      · rw [Mem.readW_writeW_self32, U.gpr]

/-- The 176 bytes below `sp`, from their base: the callee's 96 below its `esp`, then its frame of 76. -/
theorem below176_parts {sp : BitVec 32} (low : 176 ≤ sp.toNat) :
    ((sp - BitVec.ofNat 32 80).setWidth 64 = (sp - BitVec.ofNat 32 176).setWidth 64 + BitVec.ofNat 64 96) ∧
      below (sp - BitVec.ofNat 32 80) 96 = ⟨(sp - BitVec.ofNat 32 176).setWidth 64, 96⟩ := by
  have := sp.isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  · simp only [below]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith

/-- The callee's inputs: those of the caller, read from the frame of the copied arguments at `esp`,
80 bytes below the caller's. -/
theorem in_callee {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} {s f : State} (h : In Ex base bytes len args s)
    (RF : RoomF (s.gpr .esp) base bytes) (ef : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80)
    (edi : f.gpr .edi = s.gpr .edi) (rd : f.rd = s.rd)
    (wr : f.wr = ⟨(f.gpr .esp).setWidth 64, 76⟩ :: s.wr)
    (vals : ∀ i < 18, f.mem.readW (slotAddr ((f.gpr .esp).setWidth 64) i) 32 = args i) :
    In (fun _ _ => True) base bytes len args f := by
  have low := RF.low
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain ⟨e1, e2⟩ := below176_parts low
  obtain fN : (f.gpr .esp).toNat = (s.gpr .esp).toNat - 80 := by
    rw [ef]; exact VG.X86.sub_toNat (by omega_using [low])
  generalize hX : (s.gpr .esp - BitVec.ofNat 32 176).setWidth 64 = X at e1 e2
  obtain b176 : below (s.gpr .esp) 176 = ⟨X, 176⟩ := by rw [← hX]
  obtain fP : (f.gpr .esp).setWidth 64 = X + BitVec.ofNat 64 96 := by rw [ef, e1]
  obtain frameSub : Region.Sub ⟨(f.gpr .esp).setWidth 64, 76⟩ (below (s.gpr .esp) 176) := by
    rw [fP, b176]
    have := Offset.sub X (d := 96) (n := 76) (e := 0) (k := 176) (by decide) (by decide)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain frameWs : Region.Disjoint ⟨(f.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩ := RF.apart.sub_left frameSub
  obtain belowWs : Region.Disjoint (below (f.gpr .esp) 96) ⟨base, bytes⟩ := by
    rw [ef, e2]
    exact RF.apart.sub_left (by rw [b176]; exact Region.sub_prefix (by decide))
  obtain SA : ∀ i < 18, VG.Proof.Dsa.X86.stackAddress f i = slotAddr ((f.gpr .esp).setWidth 64) i :=
    fun i hi => addr_eq (by omega_using [fN, hi, top])
  refine ⟨⟨by rw [edi]; exact h.scratch.edi, by rw [wr]; exact List.mem_cons_of_mem _ h.scratch.wr, nw, ?_⟩,
    h.lower, h.upper, fun i hi => ⟨⟨?_, ?_⟩, ?_⟩, h.outLen, ⟨by rw [fN]; omega_using [low], belowWs⟩,
    by rw [fN]; omega_using [top], h.need, h.hbase, h.hbytes, trivial⟩
  · refine VG.Proof.Weierstrass.X86.stkOk_of (z := 96) (by decide) (by rw [fN]; omega_using [low]) nw
      (by have := h.need; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega_using [this]) ?_
    have e := belowWs
    simp only [below] at e
    rwa [VG.X86.Taint.sub_setWidth (by rw [fN]; omega_using [low])] at e
  · rw [SA i hi, rd, wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [SA i hi]; exact frameWs.sub_left (Offset.sub_base _ (by omega_using [hi]))
  · show f.mem.readW (VG.Proof.Dsa.X86.stackAddress f i) 32 = args i
    rw [SA i hi]; exact vals i hi

end VG.Proof.Ffdh.X86

end
