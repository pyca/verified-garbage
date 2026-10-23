module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Column
import VerifiedGarbage.Proof.Framework.Omega

/-! # All the columns

`columns` clears the carry and runs the `2 N` columns (`columns_ok`): after
them `ColsI` holds for `k = 2 N`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

theorem columns_ok {s0 : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (hw : Ws s0 W L) (P : Params s0 W L V 12) :
    WP isa columns s0 fun u => ∃ c, ColsI s0 W L V N S mo a b (2 * N) c u := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  unfold columns
  simp only [offC]
  refine WP.seq (wp_movX (P.read pS (by decide)) fun t1 u1 m1 x1 => wp_movX rfl fun t2 u2 m2_1 x2 => ?_)
  have b2 : PtrAt t2 W .ebx S := by rw [PtrAt, u2.other _ (by decide)]; exact ptr_of_param u1.gpr PV.s
  have K2 : Keeps [.eax, .ebx] s0 t2 := (u1.keeps.mono (by decide)).widen u2.keeps
  have hw2 := hw.of_keeps K2
  refine wp_storeX (ea_ptr hw2 b2 (d := 16) (by omega_using [hs])) (ws_write hw2 (y := S + 16) (n := 4)
    (by omega_using [hs])) fun t3 M3 m3 x3 => ?_
  have hw3 := hw2.of_wr M3.wr
  have b3 : PtrAt t3 W .ebx S := by rw [PtrAt, M3.gpr]; exact b2
  refine wp_storeX (ea_ptr hw3 b3 (d := 20) (by omega_using [hs])) (ws_write hw3 (y := S + 20) (n := 4)
    (by omega_using [hs])) fun t4 M4 m4 x4 => wp_movX rfl fun t5 u5 m5 x5 => WP.block_nil ?_
  have K5 : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s0 t5 :=
    (((K2.mono (by decide)).widen (M3.keeps [])).widen (M4.keeps [])).widen u5.keeps
  have mem5 : t5.mem = (t2.mem.writeW (off W (S + 16)) (t2.gpr .eax)).writeW (off W (S + 20)) (t3.gpr .eax) := by
    rw [u5.mem, M4.mem, M3.mem]
  have e2 : t2.gpr .eax = 0 := u2.gpr
  have e3 : t3.gpr .eax = 0 := by rw [M3.gpr, e2]
  have O1 : Outside W (S + 16) 4 t2.mem (t2.mem.writeW (off W (S + 16)) (t2.gpr .eax)) :=
    writeW32_outside _ _ _ (by omega_using [hs, hn])
  have O2 : Outside W (S + 20) 4 (t2.mem.writeW (off W (S + 16)) (t2.gpr .eax))
      ((t2.mem.writeW (off W (S + 16)) (t2.gpr .eax)).writeW (off W (S + 20)) (t3.gpr .eax)) :=
    writeW32_outside _ _ _ (by omega_using [hs, hn])
  have m2 : t2.mem = s0.mem := by rw [u2.mem, u1.mem]
  have O5 : Outs W [(S, 8 * N + 28)] s0.mem t5.mem := by
    rw [mem5, ← m2]
    exact (Outs.of_outside (O1.mono (o' := S) (n' := 8 * N + 28) (by omega_using []) (by omega_using [])) (by simp)).trans
      (Outs.of_outside (O2.mono (o' := S) (n' := 8 * N + 28) (by omega_using []) (by omega_using [])) (by simp))
  have I0 : ColsI s0 W L V N S mo a b 0 0 t5 := by
    refine ⟨hw.of_keeps K5, P.keep (outs_sub1 O5 (List.mem_singleton_self (0, L)) (Nat.zero_le _)
        (by simp only; omega_using [hs])) (K5.1 _ (by decide)) K5.2.1 K5.2.2, O5, u5.gpr,
      by rw [m5, m4, m3, m2_1, m1], ?_, Nat.zero_le _, ?_, K5⟩
    · rw [mem5, w32_write_ne (size := L) (o := S + 20) (d := S + 16) hn (by omega_using [hs])
        (by omega_using [hs]) (by omega_using []), w32_write_self, w32_write_self, e2, e3]; rfl
    · simp [Column.partSum_zero, val32]
  refine WP.loop (M := isa) (fun m u => ∃ k c, m = 2 * N - k ∧ k < 2 * N ∧ ColsI s0 W L V N S mo a b k c u)
    ?_ (2 * N) t5 ⟨0, 0, rfl, by omega_using [hN], I0⟩
  rintro m u ⟨k, c, rfl, hk, I⟩
  refine WP.mono (column_ok Ly PV hinv hm0 I hk) fun v ⟨c', I', z⟩ => ?_
  have hv : isa.eval .ne v = some (!decide (k + 1 = 2 * N)) := by show v.zf.map _ = _; rw [z]; rfl
  by_cases h : k + 1 = 2 * N
  · exact .inl ⟨by rw [hv, decide_eq_true h]; rfl, c', h ▸ I'⟩
  · exact .inr ⟨by rw [hv, decide_eq_false h]; rfl, 2 * N - (k + 1), by omega_using [hk],
      k + 1, c', rfl, by omega_using [hk, h], I'⟩

end VG.Proof.Mont.X86.Sse2
