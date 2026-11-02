module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Core
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Pack
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the functions

`fn k core` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`, each
number below the own working space at `8192 - 64 k` (`fn_ok`): `core` on the
pointers if they are multiples of 8, else on byte-wise copies in the own
working space, as P-384's (`Proof/Weierstrass/RISCV64/P384Field/Fn.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx Rest limb wd wd_shift in_base)
open VG.Proof.X448.RISCV64.R64 (dw al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (ptr_mod8 aligned_of zext_ok)

theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The working space at `W`, `a3 = W + 6144`. -/
structure WsW (W : Addr) (s : State) : Prop where
  al : W.toNat % 8 = 0
  wr : (⟨W, 8192⟩ : Region) ∈ s.wr
  nowrap : W.toNat + 8192 ≤ 2 ^ 64
  a3 : s.gpr .a3 = W + BitVec.ofNat 64 6144

theorem WsW.ctx {W : Addr} {s : State} (h : WsW W s) : Ctx (W + BitVec.ofNat 64 6144) s :=
  ⟨h.a3, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.al; omega, fun d n hd => by
    rw [off_add]; exact in_base h.wr (by omega) (by omega)⟩

theorem WsW.bnowrap {W : Addr} {s : State} (h : WsW W s) :
    (W + BitVec.ofNat 64 6144).toNat + 2048 ≤ 2 ^ 64 := by
  have := h.nowrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 6144 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- What the pointers' block leaves, after the zero-extension from `σ`. -/
theorem ptrs_ok {W : Addr} {σ s : State} (hz : VG.Proof.Ed25519.RISCV64.zextF σ s) (h0 : σ.gpr .a0 = W) :
    WP isa (.block ptrs) s fun t =>
      t.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) ∧ t.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) ∧
      t.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) ∧ t.gpr .a3 = W + BitVec.ofNat 64 6144 ∧
      t.gpr .t0 = ((W + BitVec.ofNat 64 (lo σ .a1)) ||| (W + BitVec.ofNat 64 (lo σ .a2)) |||
        (W + BitVec.ofNat 64 (lo σ .a3))) &&& BitVec.ofInt 64 7 ∧
      Rest [.a3, .t0, .t2, .t4, .t5] s t ∧ t.mem = s.mem := by
  obtain ⟨-, e0, ek⟩ := hz
  have e1 := ek .a1 (by simp)
  have e2 := ek .a2 (by simp)
  have e3 := ek .a3 (by simp)
  rw [h0] at e0
  simp only [ptrs]
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_addi (by decide) fun s10 u10 =>
    wp_addi (by decide) fun s11 u11 => wp_addi (by decide) fun s12 u12 => wp_addi (by decide) fun s13 u13 =>
    wp_or fun s14 u14 => wp_or fun s15 u15 =>
    wp_andi (by decide) fun s16 u16 => WP.block_nil ?_
  have p2 : s9.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, e0, e1]
  have p4 : s9.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) := by
    rw [u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u7.other .a2 (by decide), e0, e2]
  have p5 : s9.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) := by
    rw [u9.gpr, u8.other _ (by decide), u8.other .a3 (by decide), u7.other _ (by decide),
      u7.other .a3 (by decide), e0, e3]
  have g16 : ∀ r, r ≠ .t0 → r ≠ .a3 → s16.gpr r = s9.gpr r := fun r h0 h3 => by
    rw [u16.other _ h0, u15.other _ h0, u14.other _ h0, u13.other _ h3, u12.other _ h3, u11.other _ h3,
      u10.other _ h3]
  refine ⟨by rw [g16 _ (by decide) (by decide), p2], by rw [g16 _ (by decide) (by decide), p4],
    by rw [g16 _ (by decide) (by decide), p5], ?_, ?_, ?_, ?_⟩
  · rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.gpr, u12.gpr, u11.gpr,
      u10.gpr, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), e0, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.add_assoc]
    rfl
  · rw [u16.gpr, u15.gpr, u14.gpr, u14.other .t5 (by decide)]
    rw [u13.other .t2 (by decide), u13.other .t4 (by decide), u13.other .t5 (by decide),
      u12.other .t2 (by decide), u12.other .t4 (by decide), u12.other .t5 (by decide),
      u11.other .t2 (by decide), u11.other .t4 (by decide), u11.other .t5 (by decide), u10.other .t2 (by decide),
      u10.other .t4 (by decide), u10.other .t5 (by decide), p2, p4, p5]
  · exact (u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
      ((u13.rest (by decide)).trans ((u14.rest (by decide)).trans ((u15.rest (by decide)).trans
      (u16.rest (by decide))))))))))
  · rw [u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]

/-! ## The operations as specifications -/

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res`, written at `[t2]`. -/
def CoreSpec (k : Nat) (core : List Instr) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {b A B O : Addr} {s : State}, CoreOk k b A B O s → pre (xv s.mem A k) (xv s.mem B k) →
    WP isa (.block core) s fun s' => res (xv s.mem A k) (xv s.mem B k) (ov s'.mem O k) ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem mulCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k))
    (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1) :
    CoreSpec k (mulCore k m) (fun _ B => B < m) (fun A B r => r < m ∧ r * 2 ^ (64 * k) % m = A * B % m) :=
  fun hC hB => WP.mono (mulCore_ok hC hm hinv hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k)) :
    CoreSpec k (addCore k m) (fun A B => A + B < 2 * m) (fun A B r => r = (A + B) % m) :=
  fun hC hAB => WP.mono (addCore_ok hC hm hAB) fun _ ⟨g, rd, wr, sp, f, v⟩ => ⟨v, f, g, rd, wr, sp⟩

theorem subCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k)) :
    CoreSpec k (subCore k m) (fun A B => A < m ∧ B < m) (fun A B r => r = (A + m - B) % m) :=
  fun hC hAB => WP.mono (subCore_ok hC hm hAB.1 hAB.2) fun _ ⟨g, rd, wr, sp, f, v⟩ => ⟨v, f, g, rd, wr, sp⟩

/-! ## The byte-wise copies -/

theorem layout_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) :
    6144 + T k = 8192 - 64 * k ∧ SA k = N k + 8 * k ∧ SB k = SA k + 8 * k ∧ SO k = SB k + 8 * k ∧
      SO k + 8 * k ≤ 2048 ∧ N k + 8 * k = T k + 8 * (2 * k + 2) := by
  unfold SO SB SA N T; omega

/-- The `k` doublewords at `b + o` are the words that `unpack` or `pack` copied. -/
theorem xv_of_limbs {k : Nat} {m m' : Mem} {b P : Addr} {o : Nat}
    (h : ∀ i < 2 * k, limb m' b o i = wd m P (0 + 4 * i)) : xv m' (b + BitVec.ofNat 64 o) k = xv m P k :=
  dv_congr_wd fun j hj => by rw [wd_shift, ← limb, h j hj, Nat.zero_add]

theorem xv_of_wds {k : Nat} {m m' : Mem} {b P : Addr} {o : Nat}
    (h : ∀ i < 2 * k, wd m' P (0 + 4 * i) = limb m b o i) : xv m' P k = xv m (b + BitVec.ofNat 64 o) k :=
  dv_congr_wd fun j hj => by rw [← Nat.zero_add (4 * j), h j hj, limb, wd_shift, Nat.zero_add]

theorem dw_frame1 {m m' : Mem} {R : Region} (hf : Frame [R] m m') {P : Addr} {d : Nat}
    (hd : Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ R) : dw m' P d = dw m P d :=
  VG.Proof.X448.RISCV64.R64.dw_frame hf fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd

/-- The `k` doublewords at `W + x` through a frame of a region `W + e` apart from them. -/
theorem xv_frame {k : Nat} {m m' : Mem} {W : Addr} {x e n : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, n⟩] m m')
    (hd : x + 8 * k ≤ e ∨ e + n ≤ x) (hx : x + 8 * k ≤ 2 ^ 64) (he : e + n ≤ 2 ^ 64) :
    xv m' (W + BitVec.ofNat 64 x) k = xv m (W + BitVec.ofNat 64 x) k :=
  colsV_congr fun i hi => dw_frame1 hf (by rw [off_add]; exact Offset.disjoint W (by omega) (by omega) he)

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {k : Nat} {W : Addr} {s : State} (hw : WsW W s) (hk : 7 ≤ k) (hk' : k ≤ 30) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 8 * k ≤ 8192 - 64 * k) (hb : bb + 8 * k ≤ 8192 - 64 * k) :
    WP isa (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack k .t4 (SA k) 0 ++
        unpack k .t5 (SB k) 0 ++ ([.addi .t4 .a3 (SA k), .addi .t5 .a3 (SB k), .addi .t2 .a3 (SO k)] : List Instr))) s
      fun t => WsW W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧
        t.gpr .t4 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k) ∧
        t.gpr .t5 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k) ∧
        t.gpr .t2 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SO k) ∧
        xv t.mem (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k)) k = xv s.mem (W + BitVec.ofNat 64 a) k ∧
        xv t.mem (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k)) k = xv s.mem (W + BitVec.ofNat 64 bb) k ∧
        Frame [⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k), 8 * k⟩,
          ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k), 8 * k⟩] s.mem t.mem ∧
        Rest [.t1, .t2, .t4, .t5, .a4, .a5] s t := by
  obtain ⟨e6, eA, eB, eO, otop, -⟩ := layout_facts k (by omega) hk'
  obtain ⟨hNT, -, -⟩ := N_facts k (by omega) hk'
  obtain ⟨t8, -⟩ := T_facts k (by omega) hk'
  have hnw := hw.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => ?_
  have hw1 : WsW W s1 := ⟨hw.al, by rw [u1.wr]; exact hw.wr, hnw, by rw [u1.other _ (by decide), hw.a3]⟩
  refine WP.block_append (WP.mono (unpack_ok (k := k) hw1.ctx (p := .t4) (q := W + BitVec.ofNat 64 a) (by decide)
    (by rw [u1.other _ (by decide), h4]) (o := SA k) (src := 0) (by omega) (by unfold SA N T; omega) (by omega)
    (fun j hj => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw1.wr (d := a + 4 * j) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)))
    fun s2 ⟨r2, f2, v2⟩ => ?_)
  have hw2 : WsW W s2 := ⟨hw.al, by rw [r2.wr]; exact hw1.wr, hnw, by rw [r2.gpr _ (by decide), hw1.a3]⟩
  refine WP.block_append (WP.mono (unpack_ok (k := k) hw2.ctx (p := .t5) (q := W + BitVec.ofNat 64 bb) (by decide)
    (by rw [r2.gpr _ (by decide), u1.other _ (by decide), h5]) (o := SB k) (src := 0) (by omega)
    (by unfold SB SA N T; omega) (by omega)
    (fun j hj => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw2.wr (d := bb + 4 * j) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hw3 : WsW W s3 := ⟨hw.al, by rw [r3.wr]; exact hw2.wr, hnw, by rw [r3.gpr _ (by decide), hw2.a3]⟩
  refine wp_addi (by omega) fun s4 u4 => wp_addi (by omega) fun s5 u5 => wp_addi (by omega) fun s6 u6 =>
    WP.block_nil ?_
  have r6 : Rest [.t1, .t2, .t4, .t5, .a4, .a5] s s6 :=
    (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have sep : Region.Disjoint ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k), 8 * k⟩
      ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k), 8 * k⟩ := by
    rw [off_add, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  refine ⟨⟨hw.al, by rw [r6.wr]; exact hw.wr, hnw, by rw [r6.gpr _ (by decide), hw.a3]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hw3.a3]
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), hw3.a3]
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), hw3.a3]
  · rw [m6, off_add, xv_frame (k := k) (by rw [off_add] at f3; exact f3) (by omega) (by omega) (by omega),
      ← off_add, xv_of_limbs (k := k) v2, u1.mem]
  · rw [m6, xv_of_limbs (k := k) v3,
      xv_frame (k := k) (by rw [off_add] at f2; exact f2) (by omega) (by omega) (by omega), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2.mono (by simp)).trans (f3.mono (by simp))

end VG.Proof.Weierstrass.RISCV64.GenWide
