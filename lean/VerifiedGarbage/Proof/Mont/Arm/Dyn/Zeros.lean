module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: clearing words

`zeros k o` clears `k` words at `[o]` through `r10`, up to `r9` (`zeros_ok`).
Pointers that loops move through the working space (`at_ptr`), and stores
into a range (`Outside.write32`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str op2_imm)

/-- A pointer `step·j` bytes past `K` bytes into the working space. -/
theorem at_ptr {t : State} {p : Reg} {B : BitVec 32} {K x : Nat} (hp : t.gpr p = B + BitVec.ofNat 32 K + BitVec.ofNat 32 x)
    (hB : t.gpr .r12 = B) : t.gpr p = t.gpr .r12 + BitVec.ofNat 32 (K + x) := by
  rw [hp, hB, Offset.add_add]

/-- A pointer `K` bytes into the working space. -/
theorem at_ptr' {t : State} {p : Reg} {B : BitVec 32} {K : Nat} (hp : t.gpr p = B + BitVec.ofNat 32 K)
    (hB : t.gpr .r12 = B) : t.gpr p = t.gpr .r12 + BitVec.ofNat 32 K := by
  rw [hp, hB]

/-- A pointer moved up a step. -/
theorem ptr_step {x B : BitVec 32} {K st j : Nat} (h : x = B + BitVec.ofNat 32 K + BitVec.ofNat 32 (st * j)) :
    x + BitVec.ofNat 32 st = B + BitVec.ofNat 32 K + BitVec.ofNat 32 (st * (j + 1)) := by
  rw [h, Offset.add_add, Offset.add_add, Offset.add_add, Nat.mul_succ]

/-- A store inside the range that may change. -/
theorem _root_.VG.Proof.Mont.Outside.write32 {base : Addr} {o n d : Nat} {m₀ m : Mem} (h : Outside base o n m₀ m)
    (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : o + n ≤ 2 ^ 64) (v : BitVec 32) :
    Outside base o n m₀ (m.writeW (off base d) v) :=
  h.trans ((writeW32_outside _ _ _ (by omega)).mono h₁ h₂)

theorem w32_write_lt {m : Mem} {base : Addr} {o d : Nat} (hn : base.toNat + o + 4 ≤ 2 ^ 32)
    (hd : d + 4 ≤ o) (v : BitVec 32) : w32 (m.writeW (off base o) v) base d = w32 m base d :=
  w32_write_ne (size := o + 4) (by omega) (by omega) (by omega) (.inl hd) v

/-- `[o] = 0`, `k` words. -/
theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o k : Nat}
    (hk : 0 < k) (hok : o + 4 * k ≤ size) (h16 : o + 4 * k < 2 ^ 16) :
    WP isa (Dynamic.zeros k o) s fun t => Ws t base size ∧ (∀ j < k, w32 t.mem base (o + 4 * j) = 0) ∧
      Outside base o (4 * k) s.mem t.mem ∧ Rest [.r7, .r9, .r10] s t := by
  have hn := hs.nowrap
  unfold Dynamic.zeros
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega) fun s₁ u₁ =>
    wp_ptr (d := .r9) (by decide) (by omega) fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun t u₃ => WP.block_nil ?_)
  have R : Rest [.r7, .r9, .r10] s t :=
    ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))
  have wt : Ws t base size := hs.of_rest R (by decide)
  have r7 : t.gpr .r7 = 0 := u₃.gpr
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have p0 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (o + 4 * k) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other .r12 (by decide)]
  clear u₁ u₂ u₃
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 o) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ u.gpr .r7 = 0 ∧ Rest [.r7, .r9, .r10] s u ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) = 0) ∧ Outside base o (4 * k) s.mem u.mem)
    (by decide) hk (by omega) (fun j u u' ⟨a, b, c, d, e⟩ f => ⟨a.of_fupd f, by rw [f.gpr]; exact b,
      c.trans (f.rest _), by rw [f.mem]; exact d, by rw [f.mem]; exact e⟩)
    ⟨wt, r7, R, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p0 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, _, c, d, e⟩ _ => ⟨a, d, e, c⟩
  intro j hj u ⟨wu, r7u, Ru, Vu, Ou⟩ pu p9u
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  refine wp_str (by decide) (wu.ea (K := o + 4 * j) (at_ptr pu e12) (by omega)) (wu.write (d := o + 4 * j + 0) (n := 4) (by omega))
    fun u₁ m₁ => wp_bump (by decide) fun u₂ v₂ => WP.block_nil ⟨⟨wu.of_mupd m₁ |>.of_upd v₂ (by decide), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [v₂.other .r7 (by decide), m₁.gpr]; exact r7u
  · exact (Ru.trans (m₁.rest _)).trans (v₂.rest (by simp))
  · intro i hi
    rw [v₂.mem, m₁.mem]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega) (by omega), Vu i h]
    · rw [show i = j by omega, Nat.add_zero, w32_write_self, r7u]; rfl
  · rw [v₂.mem, m₁.mem]; exact Ou.write32 (by omega) (by omega) (by omega) _
  · rw [v₂.gpr, m₁.gpr, pu, Offset.add_add, Offset.add_add, Offset.add_add]; congr 2
  · rw [v₂.other .r9 (by decide), m₁.gpr]; exact p9u

end VG.Proof.Mont.Arm.Dyn
