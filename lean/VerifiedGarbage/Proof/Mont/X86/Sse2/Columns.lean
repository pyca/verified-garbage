module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Column
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! # All the columns

`columns` copies `A` in reverse to `S + 24 + 4 N` (`copyA_ok`), clears the
carry, loads the window's first words of `M` (`window_ok`), and runs the
`2 N` columns, those with `k < N` and then the others, of the square if
`A = B` (`columns_ok`): after them `ColsI` holds for `k = 2 N`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_subXZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.zf = some (s.gpr d - v == 0) → t.mcdt = s.mcdt →
      WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl)

theorem wp_xopX (op : XOp)
    (k : ∀ t, t.gpr = s.gpr → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → t.mcdt = s.mcdt →
      t.xmm = (op.exec s).xmm → WP isa (.block is) t Q) :
    WP isa (.block (.xop op :: is)) s Q :=
  cons rfl (k _ (by cases op <;> rfl) (by cases op <;> rfl) (by cases op <;> rfl) (by cases op <;> rfl)
    (by cases op <;> rfl) rfl)

end

/-- `copyA`'s loop after `j` words. -/
structure CopyI (s : State) (W : Addr) (N S a j : Nat) (t : State) : Prop where
  keep : Keeps [.eax, .ebx, .esi, .edi] s t
  mcdt : t.mcdt = s.mcdt
  out : Outs W [(S + 24 + 4 * N, 4 * N)] s.mem t.mem
  ebx : PtrAt t W .ebx (S + 24 + 8 * N - 4 * j)
  esi : PtrAt t W .esi (a + 4 * j)
  edi : (t.gpr .edi).toNat = 4 * (N - j)
  rev : ∀ i < j, w32 t.mem W (S + 24 + 8 * N - 4 * (i + 1)) = digits s.mem W a i

theorem copyStep_ok {s t : State} {W : Addr} {L N S a j : Nat} (hw : Ws t W L) (I : CopyI s W N S a j t)
    (hj : j < N) (ha : a + 4 * N ≤ L) (hs : S + 24 + 8 * N ≤ L)
    (hsa : a + 4 * N ≤ S + 24 + 4 * N ∨ S + 24 + 8 * N ≤ a) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 0)), .alu .sub .ebx (.imm 4), .store (at_ .ebx 0) .eax,
      .alu .add .esi (.imm 4), .alu .sub .edi (.imm 4)]) t fun u =>
      CopyI s W N S a (j + 1) u ∧ u.zf = some (decide (j + 1 = N)) := by
  have hn := hw.nowrap
  refine wp_movX (readSrc_ptr hw I.esi (d := 0) (by omega_using [ha, hj])) fun t1 u1 m1 _ =>
    wp_subX rfl fun t2 u2 _ m2 _ => ?_
  have K2 : Keeps [.eax, .ebx] t t2 := (u1.keeps.mono (by decide)).widen u2.keeps
  have hw2 := hw.of_keeps K2
  have b2 : PtrAt t2 W .ebx (S + 24 + 8 * N - 4 * (j + 1)) := by
    rw [PtrAt, u2.gpr, u1.other _ (by decide), ptr_sub I.ebx _ (by rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hj])]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2
  refine wp_storeX (ea_ptr hw2 b2 (d := 0) (by omega_using [hs, hj]))
    (ws_write hw2 (y := S + 24 + 8 * N - 4 * (j + 1) + 0) (n := 4) (by omega_using [hs, hj])) fun t3 M3 m3 _ =>
    wp_addX rfl fun t4 u4 _ m4 _ => wp_subXZ rfl fun t5 u5 z5 m5 => WP.block_nil ?_
  have K5 : Keeps [.eax, .ebx, .esi, .edi] t t5 :=
    (((K2.mono (by decide)).widen (M3.keeps [])).widen u4.keeps).widen u5.keeps
  have mem5 : t5.mem = t.mem.writeW (off W (S + 24 + 8 * N - 4 * (j + 1))) (t.mem.readW (off W (a + 4 * j)) 32) := by
    rw [u5.mem, u4.mem, M3.mem, u2.other _ (by decide), u1.gpr, u2.mem, u1.mem]; simp only [Nat.add_zero]
  have edi5 : t5.gpr .edi = t.gpr .edi - 4 := by
    rw [u5.gpr, u4.other _ (by decide), M3.gpr, u2.other _ (by decide), u1.other _ (by decide)]
  obtain ⟨c1, c2⟩ := count_zf I.edi hj
  have eA : w32 t.mem W (a + 4 * j) = digits s.mem W a j :=
    Outs.w32 I.out (by simp only [List.mem_singleton, forall_eq]; omega_using [hsa, hj]) (by omega_using [ha, hj, hn])
  refine ⟨⟨I.keep.trans K5, by rw [m5, m4, m3, m2, m1, I.mcdt], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [mem5]
    exact I.out.trans (Outs.of_outside ((writeW32_outside _ _ _ (by omega_using [hs, hj, hn])).mono
      (by omega_using [hj]) (by omega_using [hj])) (List.mem_singleton_self _))
  · rw [PtrAt, u5.other _ (by decide), u4.other _ (by decide), M3.gpr]; exact b2
  · rw [PtrAt, u5.other _ (by decide), u4.gpr, M3.gpr, u2.other _ (by decide), u1.other _ (by decide),
      ptr_add I.esi]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2
  · rw [edi5]; exact c1
  · intro i hi
    rw [mem5]
    by_cases hij : i = j
    · subst hij; rw [w32_write_self]; exact eA
    · rw [w32_write_ne hn (by omega_using [hs, hj]) (by omega_using [hs, hj]) (by omega_using [hi, hij, hj])]
      exact I.rev i (by omega_using [hi, hij])
  · rw [z5, u4.other _ (by decide), M3.gpr, u2.other _ (by decide), u1.other _ (by decide), c2]

/-- `copyA`: `A` in reverse at `S + 24 + 4 N`. -/
theorem copyA_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws s W L) (P : Params s W L V 12) :
    WP isa copyA s fun u =>
      Keeps [.eax, .ebx, .esi, .edi] s u ∧ u.mcdt = s.mcdt ∧ Outs W [(S + 24 + 4 * N, 4 * N)] s.mem u.mem ∧
      ∀ i < N, w32 u.mem W (S + 24 + 4 * N + 4 * (N - 1 - i)) = digits s.mem W a i := by
  have hn := hw.nowrap
  have hN := Ly.hN
  have hs := Ly.s_le
  have ha := Ly.a_le
  have hsa : a + 4 * N ≤ S + 24 + 4 * N ∨ S + 24 + 8 * N ≤ a := by have := Ly.sa; omega_using [this]
  unfold copyA
  simp only [ld, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (ldW_ok P PV.s PV.n4 (r := .ebx) (by decide) (by decide) 0 2 fun t1 e1 _ K1 => ?_)
  refine wp_movX (P.readSk K1 (i := pA) (by decide)) fun t2 u2 m2 _ => ?_
  have P2 : Params t2 W L V 12 := (P.of_sk K1).keep (by rw [u2.mem]; exact Outs.refl _ _ _)
    (u2.other _ (by decide)) u2.rd u2.wr
  refine wp_movX (P2.read pN4 (by decide)) fun t3 u3 m3 _ => WP.block_nil ?_
  have K3 : Keeps [.eax, .ebx, .esi, .edi] s t3 := ((K1.keep.mono (by decide)).widen u2.keeps).widen u3.keeps
  have mem3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, K1.mem]
  have I0 : CopyI s W N S a 0 t3 := by
    refine ⟨K3, by rw [m3, m2, K1.mcdt], by rw [mem3]; exact Outs.refl _ _ _, ?_, ?_, ?_, fun i hi => absurd hi (by omega)⟩
    · rw [PtrAt, u3.other _ (by decide), u2.other _ (by decide), e1, BitVec.toNat_ofNat]
      congr 1; omega_using []
    · rw [PtrAt, u3.other _ (by decide), u2.gpr, PV.a, Nat.mul_zero, Nat.add_zero]
    · rw [u3.gpr, PV.n4, Nat.sub_zero]
  refine WP.mono (WP.loop (M := isa) (Q := CopyI s W N S a N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ CopyI s W N S a j t)
    ?_ N t3 ⟨0, by omega, hN, I0⟩) fun u I => ⟨I.keep, I.mcdt, I.out, fun i hi => ?_⟩
  · rintro m t ⟨j, rfl, hj, I⟩
    refine WP.mono (copyStep_ok (hw.of_keeps I.keep) I hj ha (by omega_using [hs]) hsa) fun u ⟨I', zu⟩ => ?_
    have hv : isa.eval .ne u = some (!decide (j + 1 = N)) := by show u.zf.map _ = _; rw [zu]; rfl
    by_cases h : j + 1 = N
    · exact .inl ⟨by rw [hv, decide_eq_true h]; rfl, h ▸ I'⟩
    · exact .inr ⟨by rw [hv, decide_eq_false h]; rfl, N - (j + 1), by omega_using [hj], j + 1, rfl,
        by omega_using [hj, h], I'⟩
  · rw [show S + 24 + 4 * N + 4 * (N - 1 - i) = S + 24 + 8 * N - 4 * (i + 1) by omega_using [hi]]
    exact I.rev i hi

theorem dword_zero' (i : Nat) : dword 0 i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [getLsbD_dword]

theorem Params.of_same {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (P : Params s W L V d)
    (g : t.gpr = s.gpr) (m : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Params t W L V d :=
  P.keep (by rw [m]; exact Outs.refl _ _ _) (by rw [g]) rd wr

/-- `window`: `xmm6 = 0`, and `M_1` and `M_2` (or `0`, for `N = 2`) in
doublewords 0 and 2 of `xmm7`. -/
theorem window_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws t W L) (P : Params t W L V 12) :
    WP isa window t fun u =>
      dword (u.xmm .xmm6) 0 = 0 ∧ dword (u.xmm .xmm6) 2 = 0 ∧
      (dword (u.xmm .xmm7) 0).toNat = digits t.mem W mo 1 ∧
      (dword (u.xmm .xmm7) 2).toNat = (if 3 ≤ N then digits t.mem W mo 2 else 0) ∧
      u.mem = t.mem ∧ u.mcdt = t.mcdt ∧ Keeps [.eax, .ebx] t u := by
  have hn := hw.nowrap
  have hN2 := Ly.hN2
  have hmo := Ly.mo_le
  unfold window
  refine WP.seq (wp_xopX _ fun t1 g1 m1 rd1 wr1 mc1 x1 => ?_)
  have K1 : Keeps [] t t1 := ⟨fun r _ => by rw [g1], rd1, wr1⟩
  refine wp_movX ((P.of_same g1 m1 rd1 wr1).read pM (by decide)) fun t2 u2 m2 y2 => ?_
  have hw2 := (hw.of_keeps K1).of_keeps u2.keeps
  have a2 : PtrAt t2 W .eax mo := ptr_of_param u2.gpr PV.mo
  refine wp_movX (readSrc_ptr hw2 a2 (d := 4) (by omega_using [hmo, hN2])) fun t3 u3 m3 y3 =>
    wp_xopX _ fun t4 g4 m4 rd4 wr4 mc4 x4 => ?_
  have K4 : Keeps [.eax, .ebx] t t4 :=
    (((K1.mono (by decide)).widen u2.keeps).widen u3.keeps).widen (rs := []) ⟨fun r _ => by rw [g4], rd4, wr4⟩
  have mem4 : t4.mem = t.mem := by rw [m4, u3.mem, u2.mem, m1]
  have P4 : Params t4 W L V 12 := P.keep (by rw [mem4]; exact Outs.refl _ _ _) (K4.1 _ (by decide)) K4.2.1 K4.2.2
  refine wp_movX (P4.read pN4 (by decide)) fun t5 u5 m5 x5 => wp_cmpX rfl fun t6 F6 c6 _ m6 x6 => WP.block_nil ?_
  have K6 : Keeps [.eax, .ebx] t t6 := (K4.widen u5.keeps).widen (rs := []) ⟨fun r _ => by rw [F6.gpr], F6.rd, F6.wr⟩
  have mem6 : t6.mem = t.mem := by rw [F6.mem, u5.mem, mem4]
  have mc6 : t6.mcdt = t.mcdt := by rw [m6, m5, mc4, m3, m2, mc1]
  have eM1 : (t3.gpr .ebx).toNat = digits t.mem W mo 1 := by
    rw [u3.gpr, u2.mem, m1]; rfl
  have x6_6 : t6.xmm .xmm6 = 0 := by
    rw [x6, x5, x4]
    simp only [XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte]
    rw [y3, y2, x1]
    simp only [XOp.exec, xmm_setXmm, ↓reduceIte, pxor_self]
  have x7_6 : t6.xmm .xmm7 = (0 : BitVec 96) ++ t3.gpr .ebx := by
    rw [x6, x5, x4]
    simp only [XOp.exec, xmm_setXmm, ↓reduceIte]
  have cf6 : t6.cf = some (decide (N < 3)) := by
    rw [c6, u5.gpr, PV.n4]
    show some (decide (4 * N < 12)) = _
    congr 1; exact decide_eq_decide.mpr (by omega)
  have eax6 : PtrAt t6 W .eax mo := by
    rw [PtrAt, F6.gpr, u5.other _ (by decide), g4, u3.other _ (by decide)]; exact a2
  refine WP.ite (decide (N < 3)) cf6 ?_ ?_
  · intro h3
    have h3' : ¬ 3 ≤ N := by have := of_decide_eq_true h3; omega
    refine WP.block_nil ⟨by rw [x6_6]; exact dword_zero' 0, by rw [x6_6]; exact dword_zero' 2, ?_, ?_, mem6, mc6, K6⟩
    · rw [x7_6, dword_movd_0, eM1]
    · rw [x7_6, dword_movd_2, ite_eq_right h3']; rfl
  · intro h3
    have h3' : 3 ≤ N := by have := of_decide_eq_false h3; omega
    have hw6 := hw.of_keeps K6
    refine wp_movX (readSrc_ptr hw6 eax6 (d := 8) (by omega_using [hmo, h3'])) fun t7 u7 m7 y7 =>
      wp_xopX _ fun t8 g8 m8 rd8 wr8 mc8 x8 => wp_xopX _ fun t9 g9 m9 rd9 wr9 mc9 x9 => WP.block_nil ?_
    have x9_7 : t9.xmm .xmm7 = XBinOp.eval .punpcklqdq (t6.xmm .xmm7) ((0 : BitVec 96) ++ t7.gpr .ebx) := by
      rw [x9]
      simp only [XOp.exec, xmm_setXmm, ↓reduceIte, x8, reduceCtorEq, y7]
    have x9_6 : t9.xmm .xmm6 = t6.xmm .xmm6 := by
      rw [x9]
      simp only [XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, x8, y7]
    refine ⟨by rw [x9_6, x6_6]; exact dword_zero' 0, by rw [x9_6, x6_6]; exact dword_zero' 2, ?_, ?_,
      by rw [m9, m8, u7.mem, mem6], by rw [mc9, mc8, m7, mc6],
      (K6.widen u7.keeps).widen (rs := []) ⟨fun r _ => by rw [g9, g8], by rw [rd9, rd8], by rw [wr9, wr8]⟩⟩
    · rw [x9_7, dword_punpcklqdq_0, x7_6, dword_movd_0, eM1]
    · rw [x9_7, dword_punpcklqdq_2, dword_movd_0, ite_eq_left h3', u7.gpr, mem6]; rfl

/-- The columns of one kind: `k < N`, then the others. -/
theorem phases_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (sq : Bool) (hsq : sq = true → a = b) (I : ColsI s0 W L V N S mo a b 0 c q t) :
    WP isa (phases sq) t fun u => ∃ c q, ColsI s0 W L V N S mo a b (2 * N) c q u := by
  have hN := Ly.hN
  unfold phases
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun u => ∃ c q, ColsI s0 W L V N S mo a b N c q u)
    (fun m u => ∃ k c q, m = N - k ∧ k < N ∧ ColsI s0 W L V N S mo a b k c q u) ?_ N t
    ⟨0, c, q, (Nat.sub_zero N).symm, hN, I⟩) ?_)
  · rintro m u ⟨k, c, q, rfl, hk, I⟩
    refine WP.mono (column_ok Ly PV hinv hm0 I (by omega_using [hk]) sq false hsq
      (by simp only [Bool.false_eq_true, false_iff]; omega_using [hk])) fun v ⟨c', q', I', z⟩ => ?_
    simp only [Bool.false_eq_true, ↓reduceIte] at z
    have hv : isa.eval .ne v = some (!decide (k + 1 = N)) := by show v.zf.map _ = _; rw [z]; rfl
    by_cases h : k + 1 = N
    · exact .inl ⟨by rw [hv, decide_eq_true h]; rfl, c', q', h ▸ I'⟩
    · exact .inr ⟨by rw [hv, decide_eq_false h]; rfl, N - (k + 1), by omega_using [hk], k + 1, c', q', rfl,
        by omega_using [hk, h], I'⟩
  · rintro u ⟨c, q, I⟩
    refine WP.loop (M := isa)
      (fun m u => ∃ k c q, m = 2 * N - k ∧ N ≤ k ∧ k < 2 * N ∧ ColsI s0 W L V N S mo a b k c q u) ?_ (2 * N - N) u
      ⟨N, c, q, rfl, Nat.le_refl _, by omega_using [hN], I⟩
    rintro m u ⟨k, c, q, rfl, hkN, hk, I⟩
    refine WP.mono (column_ok Ly PV hinv hm0 I hk sq true hsq (iff_of_true rfl hkN)) fun v ⟨c', q', I', z⟩ => ?_
    simp only [↓reduceIte] at z
    have hv : isa.eval .ne v = some (!decide (k + 1 = 2 * N)) := by show v.zf.map _ = _; rw [z]; rfl
    by_cases h : k + 1 = 2 * N
    · exact .inl ⟨by rw [hv, decide_eq_true h]; rfl, c', q', h ▸ I'⟩
    · exact .inr ⟨by rw [hv, decide_eq_false h]; rfl, 2 * N - (k + 1), by omega_using [hk], k + 1, c', q', rfl,
        by omega_using [hkN], by omega_using [hk, h], I'⟩

theorem columns_ok {s0 : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (hw : Ws s0 W L) (P : Params s0 W L V 12) :
    WP isa columns s0 fun u => ∃ c q, ColsI s0 W L V N S mo a b (2 * N) c q u := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  have hsmo : mo + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ mo := Ly.smo
  unfold columns
  simp only [seqs, offC]
  refine WP.seq (WP.mono (copyA_ok Ly PV hw P) fun t1 ⟨K1, mc1, O1, R1⟩ => ?_)
  have O1' : Outs W [(0, L)] s0.mem t1.mem := outs_sub1 O1 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_using [hs])
  have P1 : Params t1 W L V 12 := P.keep O1' (K1.1 _ (by decide)) K1.2.1 K1.2.2
  have hw1 := hw.of_keeps K1
  refine WP.seq (wp_movX (P1.read pS (by decide)) fun t2 u2 m2 _ => wp_movX rfl fun t3 u3 m3 _ => ?_)
  have b3 : PtrAt t3 W .ebx S := by rw [PtrAt, u3.other _ (by decide)]; exact ptr_of_param u2.gpr PV.s
  have K3 : Keeps [.eax, .ebx] t1 t3 := (u2.keeps.mono (by decide)).widen u3.keeps
  have hw3 := hw1.of_keeps K3
  refine wp_storeX (ea_ptr hw3 b3 (d := 16) (by omega_using [hs])) (ws_write hw3 (y := S + 16) (n := 4)
    (by omega_using [hs])) fun t4 M4 m4 _ => ?_
  have hw4 := hw3.of_wr M4.wr
  have b4 : PtrAt t4 W .ebx S := by rw [PtrAt, M4.gpr]; exact b3
  refine wp_storeX (ea_ptr hw4 b4 (d := 20) (by omega_using [hs])) (ws_write hw4 (y := S + 20) (n := 4)
    (by omega_using [hs])) fun t5 M5 m5 _ => wp_movX rfl fun t6 u6 m6 _ => WP.block_nil ?_
  have K6 : Keeps [.eax, .ebx, .ecx] t1 t6 :=
    (((K3.mono (by decide)).widen (M4.keeps [])).widen (M5.keeps [])).widen u6.keeps
  have e3 : t3.gpr .eax = 0 := u3.gpr
  have e4 : t4.gpr .eax = 0 := by rw [M4.gpr, e3]
  have mem3 : t3.mem = t1.mem := by rw [u3.mem, u2.mem]
  have mem6 : t6.mem = (t1.mem.writeW (off W (S + 16)) (0 : BitVec 32)).writeW (off W (S + 20)) (0 : BitVec 32) := by
    rw [u6.mem, M5.mem, M4.mem, mem3, e3, e4]
  have O6 : Outs W [(S, 8 * N + 28)] t1.mem t6.mem := by
    rw [mem6]
    exact (Outs.of_outside ((writeW32_outside _ _ _ (by omega_using [hs, hn])).mono (o' := S) (n' := 8 * N + 28)
        (by omega_using []) (by omega_using [])) (List.mem_singleton_self _)).trans
      (Outs.of_outside ((writeW32_outside _ _ _ (by omega_using [hs, hn])).mono (o' := S) (n' := 8 * N + 28)
        (by omega_using []) (by omega_using [])) (List.mem_singleton_self _))
  have O6' : Outs W [(0, L)] t1.mem t6.mem := outs_sub1 O6 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_using [hs])
  have P6 : Params t6 W L V 12 := P1.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
  have hw6 := hw1.of_keeps K6
  refine WP.seq (WP.mono (window_ok Ly PV hw6 P6) fun t7 ⟨q1, q2, w1, w2, mem7, mc7, K7⟩ => ?_)
  have K7' : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s0 t7 :=
    ((K1.mono (by decide)).trans (K6.mono (by decide))).trans (K7.mono (by decide))
  have O7 : Outs W [(S, 8 * N + 28)] s0.mem t7.mem := by
    rw [mem7]
    exact (outs_sub1 O1 (List.mem_singleton_self _) (by omega_using []) (by simp only; omega_using [])).trans O6
  have P7 : Params t7 W L V 12 := P6.keep (by rw [mem7]; exact Outs.refl _ _ _) (K7.1 _ (by decide)) K7.2.1 K7.2.2
  have hmo7 : ∀ i < N, digits t7.mem W mo i = digits s0.mem W mo i := fun i hi =>
    Outs.w32 O7 (by simp only [List.mem_singleton, forall_eq]; omega_using [hsmo, hi])
      (by have := Ly.mo_le; omega_using [this, hi, hn])
  refine WP.seq (wp_movX (P7.read pA (by decide)) fun t8 u8 m8 y8 => ?_)
  refine wp_movX ((P7.keep (by rw [u8.mem]; exact Outs.refl _ _ _) (u8.other _ (by decide)) u8.rd u8.wr).read pB
    (by decide)) fun t9 u9 m9 y9 => wp_cmpX rfl fun t10 F10 _ z10 m10 y10 => WP.block_nil ?_
  have K10 : Keeps [.eax, .ebx] t7 t10 := (u8.keeps.mono (by decide)).widen u9.keeps |>.widen (rs := [])
    ⟨fun r _ => by rw [F10.gpr], F10.rd, F10.wr⟩
  have mem10 : t10.mem = t7.mem := by rw [F10.mem, u9.mem, u8.mem]
  have x10 : t10.xmm = t7.xmm := by rw [y10, y9, y8]
  have I0 : ColsI s0 W L V N S mo a b 0 0 (fun _ => 0) t10 := by
    refine ⟨hw.of_keeps (K7'.trans (K10.mono (by decide))), P7.keep (by rw [mem10]; exact Outs.refl _ _ _)
      (K10.1 _ (by decide)) K10.2.1 K10.2.2, by rw [mem10]; exact O7, ?_,
      by rw [m10, m9, m8, mc7, m6, m5, m4, m3, m2, mc1], ?_, Nat.zero_le _, ?_, fun _ => Nat.zero_le _,
      fun i _ h => absurd h (by omega), fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_, K7'.trans (K10.mono (by decide))⟩
    · rw [K10.1 _ (by decide), K7.1 _ (by decide), u6.gpr]; rfl
    · rw [mem10, mem7, mem6, w32_write_ne (size := L) hn (by omega_using [hs]) (by omega_using [hs])
        (by omega_using []), w32_write_self, w32_write_self]; rfl
    · intro i hi
      rw [mem10, mem7, mem6, w32_write_ne (size := L) hn (by omega_using [hs]) (by omega_using [hs, hi])
        (by omega_using [hi]), w32_write_ne (size := L) hn (by omega_using [hs]) (by omega_using [hs, hi])
        (by omega_using [hi])]
      exact R1 i hi
    · rw [x10, q1]; rfl
    · rw [x10, q2]; rfl
    · rw [x10, w1, mem10, mem7]
    · rw [x10, w2, mem10, mem7]
    · simp [Column.partSum_zero, rvalT]
  have z : isa.eval .e t10 = some (V pA - V pB == 0) := by
    show t10.zf = _; rw [z10, u9.other _ (by decide), u8.gpr, u9.gpr]
  refine WP.ite _ z (fun h => phases_ok Ly PV hinv hm0 true (fun _ => ?_) I0)
    (fun _ => phases_ok Ly PV hinv hm0 false (fun h => absurd h (by decide)) I0)
  have e : V pA = V pB := by
    rw [← BitVec.sub_add_cancel (V pA) (V pB), beq_iff_eq.mp h]; exact BitVec.zero_add _
  have := congrArg BitVec.toNat e
  rw [PV.a, PV.b] at this
  have ha := Ly.a_le
  have hb := Ly.b_le
  omega_using [this, ha, hb, hn, hN]

end VG.Proof.Mont.X86.Sse2
