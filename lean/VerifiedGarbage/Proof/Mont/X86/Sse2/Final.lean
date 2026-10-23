module

import VerifiedGarbage.Proof.Mont.X86.Sse2.Columns
public import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Column

/-! # The reduction

After the columns, `T`: the result's `N` words at `S + 24 + 4 N` and the
last carry's low word, stored after them by `top`, is below `2 M`. `subM`
writes `T - M` over the quotient digits, `Rt.mask` makes the mask from the
borrow and `T`'s top word, and `select` writes `T mod M` to `O`
(`reduction_ok`), by the run-time width multiplication's loops.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

theorem Params.of_keeps {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat}
    (h : Params s W L V d) {rs : List Reg} (K : Keeps rs s t) (O : Outs W [(0, L)] s.mem t.mem)
    (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep O (K.1 _ hsp) K.2.1 K.2.2

theorem Params.of_upd {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat}
    (h : Params s W L V d) {r : Reg} {v : BitVec 32} (u : Upd s t r v) (hr : r ≠ .esp := by decide) :
    Params t W L V d :=
  h.keep (by rw [u.mem]; exact Outs.refl _ _ _) (u.other _ (Ne.symm hr)) u.rd u.wr

/-- `T`'s top word, the carry's low word, after its `N` words. -/
theorem top_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws p W L) (P : Params p W L V 0) :
    WP isa (.block top) p fun u =>
      val32 u.mem W (S + 24 + 4 * N) (N + 1) =
        val32 p.mem W (S + 24 + 4 * N) N + 2 ^ (32 * N) * w32 p.mem W (S + 16) ∧
      Outside W (S + 24 + 8 * N) 4 p.mem u.mem ∧ Keeps [.eax, .ebx, .esi] p u := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  have hN28 := Ly.hN28
  unfold top
  simp only [offC, offW]
  refine wp_movS (P.read pS (by decide)) fun s1 u1 _ => wp_movS ((P.of_upd u1).read pN4 (by decide)) fun s2 u2 _ => ?_
  refine wp_addS rfl fun s3 u3 _ => wp_addS rfl fun s4 u4 _ => ?_
  have K4 : Keeps [.ebx, .esi] p s4 := ((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps |>.widen u4.keeps
  have hw4 := hw.of_keeps K4
  have b4 : PtrAt s4 W .ebx S := by
    rw [PtrAt, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact PV.s
  have e4 : PtrAt s4 W .esi (S + 8 * N) := by
    have := (V pN4).isLt
    rw [PtrAt, u4.gpr, u3.gpr, u3.other .ebx (by decide), u2.gpr, u2.other .ebx (by decide), u1.gpr,
      BitVec.toNat_add, BitVec.toNat_add, PV.s, PV.n4]
    omega_using [hs, hn]
  refine wp_movS (readSrc_ptr hw4 b4 (d := 16) (by omega_using [hs])) fun s5 u5 _ => ?_
  have hw5 := hw4.of_keeps u5.keeps
  have e5 : PtrAt s5 W .esi (S + 8 * N) := by rw [PtrAt, u5.other _ (by decide)]; exact e4
  refine wp_storeS (ea_ptr hw5 e5 (d := 24) (by omega_using [hs]))
    (ws_write hw5 (y := S + 8 * N + 24) (n := 4) (by omega_using [hs])) fun s6 M6 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mem5 : s5.mem = p.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    rw [M6.mem, u5.gpr, mem5, show S + 8 * N + 24 = S + 24 + 4 * N + 4 * N by omega_using [],
      val32_store hn (size := L) (by omega_using [hs]), u4.mem, u3.mem, u2.mem, u1.mem]
  · have mem5 : s5.mem = p.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    rw [M6.mem, mem5, show S + 8 * N + 24 = S + 24 + 8 * N by omega_using []]
    exact writeW32_outside _ _ _ (by omega_using [hs, hn])
  · exact (K4.mono (by decide)).widen u5.keeps |>.widen (M6.keeps [])

/-- `ptrs`: `ebx` at the quotient digits, `ebp` at `T`. -/
theorem ptrs_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (P : Params p W L V 0) :
    WP isa (.block ptrs) p fun u =>
      PtrAt u W .ebx (S + 24) ∧ PtrAt u W .ebp (S + 24 + 4 * N) ∧ u.mem = p.mem ∧ Keeps [.ebx, .ebp] p u := by
  have hs := Ly.s_le
  unfold ptrs
  simp only [offW]
  refine wp_movS (P.read pS (by decide)) fun s1 u1 _ => wp_addS rfl fun s2 u2 _ =>
    wp_movS (((P.of_upd u1).of_upd u2).read pN4 (by decide)) fun s3 u3 _ => wp_addS rfl fun s4 u4 _ => WP.block_nil ?_
  have bx : (s2.gpr .ebx).toNat = (W.toNat + (S + 24)) % 2 ^ 32 := by
    rw [u2.gpr, u1.gpr, BitVec.toNat_add, PV.s, BitVec.toNat_ofNat]; omega_using []
  refine ⟨?_, ?_, by rw [u4.mem, u3.mem, u2.mem, u1.mem],
    (((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps⟩
  · rw [PtrAt, u4.other .ebx (by decide), u3.other .ebx (by decide)]; exact bx
  · rw [PtrAt, u4.gpr, u3.gpr, u3.other .ebx (by decide), BitVec.toNat_add, bx, PV.n4]; omega_using []

/-- The reduction: `O = T mod M`, for `T` below `2 M`. -/
theorem reduction_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws p W L) (P : Params p W L V 0)
    (hT : val32 p.mem W (S + 24 + 4 * N) N + 2 ^ (32 * N) * w32 p.mem W (S + 16) < 2 * val32 p.mem W mo N) :
    WP isa (seqs [.block top, subM, .block Rt.mask, select]) p fun v =>
      val32 v.mem W o N = (val32 p.mem W (S + 24 + 4 * N) N + 2 ^ (32 * N) * w32 p.mem W (S + 16)) %
        val32 p.mem W mo N ∧
      Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] p.mem v.mem ∧ Keeps clob7 p v := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  have hmo := Ly.mo_le
  have ho := Ly.o_le
  simp only [seqs]
  refine WP.seq (WP.mono (top_ok Ly PV hw P) fun u ⟨vT, Ou, Ku⟩ => ?_)
  have Ou' : Outs W [(0, L)] p.mem u.mem :=
    Outs.of_outside (Ou.mono (o' := 0) (n' := L) (by omega_using []) (by omega_using [hs])) (by simp)
  have Pu := P.of_keeps Ku Ou'
  have hwu := hw.of_keeps Ku
  have mou : val32 u.mem W mo N = val32 p.mem W mo N :=
    Ou.val32 (by have := Ly.smo; omega_using [this]) (by omega_using [hmo, hn])
  have Tu : val32 u.mem W (S + 24 + 4 * N) N = val32 p.mem W (S + 24 + 4 * N) N :=
    Ou.val32 (by omega_using []) (by omega_using [hs, hn])
  have topu : w32 u.mem W (S + 24 + 8 * N) = w32 p.mem W (S + 16) := by
    have := vT
    rw [val32_succ, Tu, show S + 24 + 4 * N + 4 * N = S + 24 + 8 * N by omega_using []] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel this)
  -- The subtraction.
  unfold subM
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (WP.seq (WP.block_append (WP.mono (ptrs_ok Ly PV Pu) fun u1 ⟨bx1, bp1, m1, K1⟩ => ?_)))
  have Pu1 := Pu.of_keeps K1 (by rw [m1]; exact Outs.refl _ _ _)
  refine wp_movS (Pu1.read pM (by decide)) fun u2 v2 _ => wp_movS ((Pu1.of_upd v2).read pN4 (by decide))
    fun u3 v3 _ => wp_movS rfl fun u4 v4 _ => WP.block_nil ?_
  have K4 : Keeps [.ebx, .ebp, .esi, .edi, .ecx] u u4 := (((K1.mono (by decide)).widen v2.keeps).widen v3.keeps).widen
    v4.keeps
  have m4 : u4.mem = u.mem := by rw [v4.mem, v3.mem, v2.mem, m1]
  refine WP.mono (subLoop_ok (hwu.of_keeps K4) hN (src := S + 24 + 4 * N) (mo := mo) (tmp := S + 24)
    (by omega_using [hs]) hmo (by omega_using [hs]) (.inl (Nat.le_refl _)) (by have := Ly.smo; omega_using [this])
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bp1)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.gpr]; exact PV.mo)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bx1)
    (by rw [v4.other _ (by decide), v3.gpr, PV.n4]) v4.gpr) fun u5 ⟨O5, ⟨c, ec5, V5⟩, bp5, K5⟩ => ?_
  have K5u : Keeps clob7 u u5 := (K4.mono (by decide)).trans K5
  have hw5 := hwu.of_keeps K5u
  have O5' : Outs W [(0, L)] u.mem u5.mem := by
    rw [← m4]; exact Outs.of_outside (O5.mono (o' := 0) (n' := L) (by omega_using []) (by omega_using [hs])) (by simp)
  have P5 := Pu.of_keeps K5u O5'
  -- The mask.
  refine WP.seq (WP.mono (mask_ok hw5 bp5 (by omega_using [hs]) ec5) fun u6 ⟨mk, m6, K6⟩ => ?_)
  generalize hk : (!(decide (w32 u5.mem W (S + 24 + 4 * N + 4 * N) < c.toNat))) = k at mk
  have P6 := P5.of_keeps K6 (by rw [m6]; exact Outs.refl _ _ _)
  have hw6 := hw5.of_keeps K6
  -- The selection.
  unfold select
  refine WP.seq (WP.block_append (WP.mono (ptrs_ok Ly PV P6) fun u7 ⟨bx7, bp7, m7, K7⟩ => ?_))
  have P7 := P6.of_keeps K7 (by rw [m7]; exact Outs.refl _ _ _)
  refine wp_movS (P7.read pO (by decide)) fun u8 v8 _ => wp_movS ((P7.of_upd v8).read pN4 (by decide))
    fun u9 v9 _ => WP.block_nil ?_
  have K9 : Keeps [.ebx, .ebp, .esi, .edi] u6 u9 := ((K7.mono (by decide)).widen v8.keeps).widen v9.keeps
  have m9 : u9.mem = u5.mem := by rw [v9.mem, v8.mem, m7, m6]
  refine WP.mono (selLoop_ok (hw6.of_keeps K9) k hN (src := S + 24 + 4 * N) (tmp := S + 24) (o := o)
    (by omega_using [hs]) (by omega_using [hs]) ho (by have := Ly.so; omega_using [this])
    (by have := Ly.so; omega_using [this])
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bp7)
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bx7)
    (by rw [PtrAt, v9.other _ (by decide), v8.gpr]; exact PV.o)
    (by rw [v9.gpr, PV.n4])
    (by rw [v9.other _ (by decide), v8.other _ (by decide), K7.1 _ (by decide)]; exact mk))
    fun v ⟨Ov, Vv, Kv⟩ => ⟨?_, ?_, ?_⟩
  · -- The value.
    have T5 : val32 u5.mem W (S + 24 + 4 * N) N = val32 p.mem W (S + 24 + 4 * N) N := by
      rw [← Tu, ← m4]; exact O5.val32 (by omega_using []) (by omega_using [hs, hn])
    have top5 : w32 u5.mem W (S + 24 + 4 * N + 4 * N) = w32 p.mem W (S + 16) := by
      rw [← topu, show S + 24 + 4 * N + 4 * N = S + 24 + 8 * N by omega_using [], ← m4]
      exact O5.w32 (by omega_using []) (by omega_using [hs, hn])
    rw [m4, mou, Tu] at V5
    rw [m9] at Vv
    rw [top5] at hk
    have hM : val32 p.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
    have sel := csub_arith hM (val32_lt u5.mem W (S + 24) N) (by rw [← T5] at hT ⊢; omega_using [hT, T5]) (b := c)
      (top := w32 p.mem W (S + 16)) (T := val32 p.mem W (S + 24 + 4 * N) N) V5
    rw [Vv, ← hk, ← sel]
    by_cases h : w32 p.mem W (S + 16) < c.toNat <;> simp [h, T5]
  · have e1 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] p.mem u.mem :=
      Outs.of_outside (Ou.mono (o' := S + 24) (n' := 8 * N + 4) (by omega_using []) (by omega_using [])) (by simp)
    have e2 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] u.mem u5.mem := by
      rw [← m4]; exact Outs.of_outside (O5.mono (o' := S + 24) (n' := 8 * N + 4) (by omega_using []) (by omega_using []))
        (by simp)
    have e3 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] u5.mem v.mem := by
      rw [← m9]; exact Outs.of_outside Ov (by simp)
    exact (e1.trans e2).trans e3
  · exact (((((Ku.mono (by decide)).trans K5u).trans (K6.mono (by decide))).trans (K9.mono (by decide))).trans
      (Kv.mono (by decide)))

end VG.Proof.Mont.X86.Sse2
