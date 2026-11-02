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

end VG.Proof.Weierstrass.RISCV64.GenWide
