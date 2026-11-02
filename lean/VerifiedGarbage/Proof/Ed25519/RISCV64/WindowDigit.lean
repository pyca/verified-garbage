module

public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A window's digit on RISC-V

`nibble p o` leaves in `a2` nibble `s1` of the bytes at `p + o`, as the
comb's digit reads its scalar's (`nibble_ok`, `nibAt`); nibble `i` of `n` bytes is
the base-16 digit `i` of their number (`nibAt_eqN`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64

/-- Digit `i`'s nibble of the scalar at `p`. -/
def nibAt (m : Mem) (p : Addr) (i : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_lt (m : Mem) (p : Addr) (i : Nat) : nibAt m p i < 16 := Nat.mod_lt _ (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_andi' {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n &&& BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem wp_srlr {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n >>> ((s.gpr m).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftReg .srl .d d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write _ _ _))

end

theorem nibble_eq (v : Nat) (hv : v < 256) (o : Nat) :
    (BitVec.ofNat 64 v >>> (4 * o) &&& BitVec.ofInt 64 15) = BitVec.ofNat 64 (v / 16 ^ o % 16) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 := rfl
  have hl : v / 16 ^ o % 16 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h16,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega), Nat.pow_mul]

theorem counter_fact128 : ∀ i < 128,
    BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) ∧
      ((BitVec.ofNat 64 i &&& BitVec.ofInt 64 1) <<< 2).toNat % 64 = 4 * (i % 2) := by decide

/-- Nibble `i` of `n` bytes is digit `i` of their number. -/
theorem nibAt_eqN (m : Mem) (p : Addr) {n i : Nat} (hi : i < 2 * n) :
    nibAt m p i = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 16 ^ i % 16 := by
  rw [Proof.Ed25519.decodeLE_nibble, Proof.Ed25519.nibbleOf, nibAt]
  have hg : (Spec.Ed25519.bytesAt m p n).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < n by omega]
  rw [hg]
  have := (m (p + BitVec.ofNat 64 (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), Nat.pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, Nat.pow_one]; omega

theorem nibble_ok {s : State} {p : Reg} (hp : p ∉ [Reg.a1, .a2, .t0, .s1]) {P : Addr} (hP : s.gpr p = P)
    {o i : Nat} (ho : o < 2048) (hi : i < 128) (h1 : s.gpr .s1 = BitVec.ofNat 64 i)
    (hin : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o + BitVec.ofNat 64 (i / 2)) 1) :
    WP isa (.block (nibble p o)) s fun t =>
      Rest [.a1, .a2, .t0] s t ∧ t.mem = s.mem ∧
      t.gpr .a2 = BitVec.ofNat 64 (nibAt s.mem (P + BitVec.ofNat 64 o) i) := by
  have cf := counter_fact128 i hi
  have hp1 : p ≠ .s1 := fun e => hp (by simp [e])
  unfold nibble
  refine wp_srl (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  let a := P + BitVec.ofNat 64 o + BitVec.ofNat 64 (i / 2)
  have ea : s₂.gpr .a1 + BitVec.ofNat 64 o = a := by
    rw [u₂.gpr, u₁.other _ (fun e => hp (by simp [e])), hP, u₁.gpr, h1, cf.1, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 (i / 2)), ← BitVec.add_assoc]
  have hin' : InRegions (s₂.rd ++ s₂.wr) a 1 := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin
  refine wp_lbu (a := a) ho ea hin' fun s₃ u₃ => ?_
  have v_lt := (s.mem a).isLt
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have e3 : s₃.gpr .a2 = BitVec.ofNat 64 (s.mem a).toNat := by
    rw [u₃.gpr, m2]
    exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> omega)
  refine wp_andi' (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_srlr fun s₆ u₆ =>
    wp_andi' (by decide) fun t u₇ => WP.block_nil ?_
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
      (u₇.rest (by decide))))))), by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m2], ?_⟩
  rw [u₇.gpr, u₆.gpr, u₅.other .a2 (by decide), u₄.other .a2 (by decide), e3, u₅.gpr, u₄.gpr,
    u₃.other .s1 (by decide), u₂.other .s1 (by decide), u₁.other .s1 (by decide), h1, cf.2]
  rw [nibble_eq _ v_lt]
  rfl

end VG.Proof.Ed25519.RISCV64
