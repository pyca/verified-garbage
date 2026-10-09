import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareColumns
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareCopy

/-! # The Comba square in the Montgomery callee's workspace -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem square_wv_eq (m : Mem) {x : BitVec 32} {d : Nat} (hd : x.toNat + d < 2 ^ 32) :
    VG.Proof.X25519.X86.wv m x d = w32 m (x.setWidth 64) d := by
  simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd, w32, addr_eq hd, off]

theorem square_num_eq (m : Mem) {x : BitVec 32} {o : Nat} : ∀ n,
    x.toNat + o + 4 * n ≤ 2 ^ 32 →
    VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv m x (o + 4 * j)) n = val32 m (x.setWidth 64) o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [VG.Proof.X25519.X86.num_succ, square_num_eq m n (by omega), val32_succ,
      square_wv_eq m (by omega), ← Nat.pow_mul]

theorem square_frame_outside {m m' : Mem} {x : BitVec 32} {o n : Nat}
    (hx : x.toNat + o + n ≤ 2 ^ 32) (hn : 0 < n)
    (F : Frame [VG.Proof.X25519.X86.sub x o n] m m') : Outside (x.setWidth 64) o n m m' := by
  intro y hy
  apply F y
  intro r hr
  rw [List.mem_singleton.mp hr]
  simp only [VG.Proof.X25519.X86.sub, addr_eq (by omega : x.toNat + o < 2 ^ 32)]
  change ¬ ((y - (x.setWidth 64 + BitVec.ofNat 64 o)).toNat + 1 ≤ n)
  have h := (Offset.lt_iff y (x.setWidth 64) (d := o) (n := n) (by omega)).mp
  simp only [ofs] at hy
  intro h'
  have := h (by omega)
  omega

/-- The copied input is squared exactly; the saved registers and input
buffer remain outside the written product. `ebp` is restored to the base. -/
theorem squareProduct_ok {s : State} {x : BitVec 32} (hc : VG.Proof.X25519.X86.Ctx 8192 x s false) :
    WP isa (.block squareProductBase) s fun u =>
      Bx u (x.setWidth 64) 8192 ∧ VG.Proof.X25519.X86.Keep s u ∧
      Outside (x.setWidth 64) (own 4) 64 s.mem u.mem ∧
      val32 u.mem (x.setWidth 64) (own 4) 16 =
        val32 s.mem (x.setWidth 64) (tmpAt 4) 8 * val32 s.mem (x.setWidth 64) (tmpAt 4) 8 ∧
      u.gpr .ebx = 0 := by
  unfold squareProductBase
  refine WP.block_append (WP.mono (square_columns_ok hc (o := own 4) (a := tmpAt 4)
    (by decide) (by decide)) fun t ⟨K, F, V, Z⟩ => ?_)
  refine wp_movS rfl fun u R _ => WP.block_nil ?_
  have hx := hc.fit
  have hx' : (x.setWidth 64).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]
  have E : u.gpr .ebp = x := by rw [R.gpr, K.edi, hc.edi]
  have W : u.wr = s.wr := R.wr.trans K.wr
  refine ⟨⟨by rw [E], by rw [W]; exact hc.wr, by rw [hx']; exact hx⟩,
    ⟨(R.other _ (by decide)).trans K.esi, (R.other _ (by decide)).trans K.edi,
      (R.other _ (by decide)).trans K.esp, R.rd.trans K.rd, W⟩, ?_, ?_, ?_⟩
  · rw [R.mem]
    exact square_frame_outside (by change x.toNat + 3840 + 64 ≤ 2 ^ 32; omega) (by decide) F
  · rw [R.mem]
    simp only [VG.Proof.X25519.X86.fe] at V
    rw [square_num_eq _ 16 (by change x.toNat + 3840 + 4 * 16 ≤ 2 ^ 32; omega),
      square_num_eq _ 8 (by change x.toNat + 3908 + 4 * 8 ≤ 2 ^ 32; omega)] at V
    exact V
  · rw [R.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    change (t.gpr .ebx).toNat = 0
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at Z
    omega

end VG.Proof.Weierstrass.X86.Mont
