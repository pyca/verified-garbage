module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Ops
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: operands at offsets not multiples of 8

The byte-wise copies of `fn`'s other branch (`Impl/Weierstrass/RISCV64/P256Field.lean`):
the operands into `SA` and `SB` of the own working space, the pointers to
them and to `SO` (`slowIn_ok`), and the result from `SO` to `[o]`
(`slowOut_ok`), each copy as Ed25519's (`unpackField_ok`, `packField_ok`),
whose words are the four doublewords (`V_d4`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest V limb wd wd_shift wd_frame in_base)
open VG.Proof.Ed25519.RISCV64 (unpackField_ok packField_ok PackInv)

/-- The number of the words at `q`, read 32 bits at a time, is its four doublewords. -/
theorem V_zero (m : Mem) (q : Addr) : V m q 0 = d4 m q := by
  rw [V_d4]; simp

/-- `unpackField p o 0` of the operand at `W + x` into `W + 2048 + o`. -/
theorem unpack_ok {W : Addr} {s : State} (hw : WsAt W s) {p : Reg} (hp : p ∉ [Reg.a4, .a5]) {x : Nat}
    (h : s.gpr p = W + BitVec.ofNat 64 x) (hx : x + 32 ≤ 3840) {o : Nat} (ho : 1952 ≤ o) (ho' : o + 32 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (VG.Impl.Ed25519.RISCV64.unpackField p o 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 (2048 + o), 32⟩] s.mem t.mem ∧
      d4 t.mem (W + BitVec.ofNat 64 (2048 + o)) = d4 s.mem (W + BitVec.ofNat 64 x) := by
  refine WP.mono (unpackField_ok hw.ctx hp h (o := o) (src := 0) ho' ho4 (by decide)
    (fun k hk => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw.wr (d := x + 4 * k) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (by omega) (by omega) (by omega)))
    fun t ⟨r, f, v⟩ => ⟨r, by rw [off_add] at f; exact f, ?_⟩
  rw [← off_add, ← V_d4, ← V_zero]
  unfold V
  exact VG.Proof.X25519.val32_congr fun k hk => by rw [v k hk, limb]

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 32 ≤ 3840) (hb : bb + 32 ≤ 3840) :
    WP isa (.block ([.addi .t1 .t2 0] ++ VG.Impl.Ed25519.RISCV64.unpackField .t4 SA 0 ++
        VG.Impl.Ed25519.RISCV64.unpackField .t5 SB 0 ++ [.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO])) s
      fun t => WsAt W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧ t.gpr .t4 = W + BitVec.ofNat 64 4000 ∧
        t.gpr .t5 = W + BitVec.ofNat 64 4032 ∧ t.gpr .t2 = W + BitVec.ofNat 64 4064 ∧
        d4 t.mem (W + BitVec.ofNat 64 4000) = d4 s.mem (W + BitVec.ofNat 64 a) ∧
        d4 t.mem (W + BitVec.ofNat 64 4032) = d4 s.mem (W + BitVec.ofNat 64 bb) ∧
        Frame [⟨W + BitVec.ofNat 64 4000, 32⟩, ⟨W + BitVec.ofNat 64 4032, 32⟩] s.mem t.mem ∧
        Rest [.t1, .t2, .t4, .t5, .a4, .a5] s t := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => ?_
  have hw1 : WsAt W s1 := hw.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw1 (p := .t4) (by decide) (by rw [u1.other _ (by decide), h4]) ha
    (o := SA) (by decide) (by decide) (by decide)) fun s2 ⟨r2, f2, v2⟩ => ?_)
  have hw2 : WsAt W s2 := hw1.of_rest r2 (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw2 (p := .t5) (by decide)
    (by rw [r2.gpr _ (by decide), u1.other _ (by decide), h5]) hb (o := SB) (by decide) (by decide) (by decide))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hw3 : WsAt W s3 := hw2.of_rest r3 (by decide)
  refine wp_addi (by decide) fun s4 u4 => wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 =>
    WP.block_nil ?_
  have a3 : ∀ t : State, WsAt W t → t.gpr .a3 = W + BitVec.ofNat 64 2048 := fun t h => h.a3
  have r6 : Rest [.t1, .t2, .t4, .t5, .a4, .a5] s s6 :=
    (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have f2' := f2
  rw [show 2048 + SA = 4000 from rfl] at f2' v2
  rw [show 2048 + SB = 4032 from rfl] at f3 v3
  refine ⟨hw.of_rest r6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, a3 s3 hw3, off_add]; rfl
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [m6, d4_frame f3 (by omega) (by omega) (by omega), v2, u1.mem]
  · rw [m6, v3, d4_frame f2' (by omega) (by omega) (by omega), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2'.mono (by simp)).trans (f3.mono (by simp))

/-- The slow branch's copy out: `[o]` from `SO`. -/
theorem slowOut_ok {W : Addr} {s : State} (hw : WsAt W s) {o : Nat}
    (h1 : s.gpr .t1 = W + BitVec.ofNat 64 o) (ho : o + 32 ≤ 3840) :
    WP isa (.block (VG.Impl.Ed25519.RISCV64.packField .t1 SO 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem t.mem ∧
      d4 t.mem (W + BitVec.ofNat 64 o) = d4 s.mem (W + BitVec.ofNat 64 4064) := by
  refine WP.mono (packField_ok hw.ctx (p := .t1) (by decide) h1 (a := SO) (dst := 0) (by decide) (by decide)
    (by decide) (fun k hk => by
      rw [Nat.zero_add, off_add]
      exact in_base (n := 4) hw.wr (by omega) (by omega))
    (by
      rw [off_add, Nat.add_zero, off_add]
      exact Offset.disjoint W (d := o) (n := 32) (e := 2048 + SO) (k := 32) (by unfold SO; omega) (by omega)
        (by unfold SO; omega)))
    fun t ht => ⟨ht.rest, ?_, ?_⟩
  · have f := ht.frame
    rw [off_add, Nat.add_zero] at f
    exact f
  · rw [← V_zero, show (4064 : Nat) = 2048 + SO from rfl, ← off_add, ← V_d4]
    unfold V
    exact VG.Proof.X25519.val32_congr fun k hk => by rw [limb, ht.outs k hk]

end VG.Proof.Weierstrass.RISCV64.P256Field
