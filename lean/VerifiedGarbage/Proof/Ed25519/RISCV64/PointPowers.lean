module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Impl.Ed25519.RISCV64.PointMul
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field

/-!
# Ed25519 on RISCV64: tables of points in the working space

The entries of a table (`tableAt_keep`) and the slots (`env_keep`) outside
what code writes keep their values, and the address of a table's entry
(`tableAddr_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519 (powerPoint)
open VG.Proof.X25519 (val32_congr)

/-- A table entry outside a frame's regions keeps its point. -/
theorem tableAt_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 o, 128⟩ : Region).Disjoint r) : tableAt m' b o = tableAt m b o := by
  have h : ∀ c < 4, V m' b (o + 32 * c) = V m b (o + 32 * c) := fun c hc => by
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk =>
      (hd r hr).sub_left (Offset.sub b (d := o + 32 * c + 4 * k) (n := 4) (e := o) (k := 128) (by omega_arith) (by omega_arith)))
  simp only [tableAt, FS]
  rw [← Nat.add_zero o, ← Nat.mul_zero 32, h 0 (by decide), Nat.mul_zero, Nat.add_zero,
    show o + 32 = o + 32 * 1 from rfl, h 1 (by decide), show o + 64 = o + 32 * 2 from rfl, h 2 (by decide),
    show o + 96 = o + 32 * 3 from rfl, h 3 (by decide)]

/-- A slot outside a frame's regions keeps its element. -/
theorem env_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (i : Slot)
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 (offset i), 32⟩ : Region).Disjoint r) : env m' b i = env m b i := by
  have := slot_range i
  unfold env FS V
  exact congrArg _ (val32_congr (limb_frame hf fun r hr k hk =>
    (hd r hr).sub_left (Offset.sub b (d := offset i + 4 * k) (n := 4) (e := offset i) (k := 32) (by omega_arith) (by omega_arith))))

/-- `s0` at entry `n` of the table at `start`. -/
theorem tableAddr_ok {b : Addr} {s : State} (hc : Ctx8 b s) {start n : Nat} (hs : start < 2 ^ 31) (hn : n < 64)
    (h16 : s.gpr .s2 = BitVec.ofNat 64 n) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.a4, .s0] s t → t.mem = s.mem → t.gpr .s0 = b + BitVec.ofNat 64 (start + 128 * n) →
      WP isa (.block is) t Q) :
    WP isa (.block (tableAddr start ++ is)) s Q := by
  unfold tableAddr
  rw [List.append_assoc]
  refine WP.append (ByteLoad.li32_ok (d := .s0) _) fun s1 e1 => ?_
  have u1 : Upd s s1 .s0 (BitVec.ofNat 64 start) := by rw [e1, sext_ofNat hs]; exact Upd.write _ _ _
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s2 u2 => wp_sll (by decide) fun s3 u3 => wp_add fun s4 u4 => ?_
  refine k s4 ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
    (u4.rest (by decide))))) (by rw [u4.mem, u3.mem, u2.mem, u1.mem]) ?_
  rw [u4.gpr, u3.gpr, u3.other .s0 (by decide), u2.gpr, u2.other .s2 (by decide), u1.gpr,
    u1.other .a3 (by decide), u1.other .s2 (by decide), hc.a3, h16, BitVec.add_assoc,
    show BitVec.ofNat 64 n <<< 7 = BitVec.ofNat 64 (128 * n) by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith, BitVec.ofNat_add]

theorem ofNat_sub_ne_zero {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0) = decide (a ≠ c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := fun e => h (by
      have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 c := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 c), e]; simp
      have := congrArg BitVec.toNat e'
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this)
    rw [bne_iff_ne.mpr this]
    simp [h]

end VG.Proof.Ed25519.RISCV64
