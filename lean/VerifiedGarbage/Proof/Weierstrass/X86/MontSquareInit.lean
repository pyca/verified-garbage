import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareProduct

/-! # Full-product initialization for the callable x86 P-256 square -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- Equal words at different offsets represent equal numbers. -/
theorem square_val_congr {m m' : Mem} {base : Addr} {d d' : Nat} : ∀ n,
    (∀ i < n, w32 m' base (d' + 4 * i) = w32 m base (d + 4 * i)) →
    val32 m' base d' n = val32 m base d n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, square_val_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem square_zero_top {mem : Mem} {base : Addr} {o n : Nat}
    (hz : w32 mem base (o + 4 * n) = 0) : val32 mem base o (n + 1) = val32 mem base o n := by
  rw [val32_succ, hz, Nat.mul_zero, Nat.add_zero]

theorem squareInit_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (hp : Ptr s .esi a) (ha : a + 32 ≤ own 4) :
    WP isa (.block squareInit) s fun u =>
      Outside base (own 4) 100 s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own 4) 17 = val32 s.mem base a 8 * val32 s.mem base a 8 := by
  have hn := hb.nowrap
  have hown : own 4 = 3840 := rfl
  have htmp : tmpAt 4 = 3908 := rfl
  simp only [squareInit, List.append_assoc]
  refine WP.block_append (WP.mono (squareCopy_ok hb hp ha 8 (by decide)) fun t ⟨O, K, V⟩ => ?_)
  have V' := square_val_congr 8 V
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun v R _ => ?_
  have hv : v.mem = t.mem := R.mem
  have he : v.gpr .edi = s.gpr .ebp := by rw [R.gpr, K.1 _ (by decide)]
  have hc : VG.Proof.X25519.X86.Ctx 8192 (s.gpr .ebp) v false :=
    ⟨he, by rw [hb.ebp_toNat]; exact hn,
      by change (⟨(s.gpr .ebp).setWidth 64, 8192⟩ : Region) ∈ v.wr
         rw [R.wr, K.2.2, hb.ebp]; exact hb.wr, by decide, nofun⟩
  refine WP.block_append (WP.mono (squareProduct_ok hc) fun w ⟨hbw, K', O', V'', Z⟩ => ?_)
  rw [hb.ebp] at hbw O' V''
  rw [hv, V'] at V''
  refine wp_storeS (hbw.ea (d := own 4 + 64) (by omega)) (hbw.write (n := 4) (by omega))
    fun u M => WP.block_nil ?_
  have hm : u.mem = w.mem.writeW (off base (own 4 + 64)) (0 : BitVec 32) := by rw [M.mem, Z]
  have O'' := writeW32_outside w.mem base (d := own 4 + 64) (0 : BitVec 32) (by omega)
  rw [← hm] at O''
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hv] at O'
    exact ((O.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))).trans
      (O''.mono (by omega) (by omega))
  · intro r hr
    have hwE : w.gpr .ebp = s.gpr .ebp := by
      apply BitVec.eq_of_toNat_eq
      exact hbw.ebp_toNat.trans hb.ebp_toNat.symm
    cases r <;> simp at hr
    · rw [M.gpr, K'.esp, R.other _ (by decide), K.1 _ (by decide)]
    · rw [M.gpr, hwE]
    · rw [M.gpr, K'.esi, R.other _ (by decide), K.1 _ (by decide)]
  · rw [M.rd, K'.rd, R.rd, K.2.1]
  · rw [M.wr, K'.wr, R.wr, K.2.2]
  · have hz : w32 u.mem base (own 4 + 4 * 16) = 0 := by rw [hm, w32_write_self]; rfl
    rw [square_zero_top hz, O''.val32 (by omega) (by omega)]
    exact V''


end VG.Proof.Weierstrass.X86.Mont
