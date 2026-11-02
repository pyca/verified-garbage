module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarFold
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
import VerifiedGarbage.Proof.Ed25519.ScalarWord
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 on RISCV64: a 64-byte integer modulo `L`

`scalarReduceEngine` reads the 64 bytes at `t3` a word at a time, from the
top, each folded into the remainder in `a4`–`a7` (`scalarWord_ok`, by
`wordFold_ok`), and stores the integer modulo `L` at `SR` (`engine_ok`). It
writes no memory before that store, so the input may be anywhere readable.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.RISCV64.Wide (Keeps)
open VG.Spec.Ed25519 (L decodeLE bytesAt)
open VG.Proof.X448.RISCV64.R64 (dw ew sd_ok dw_write_self dw_write_other)

/-- What the scalar code writes: the remainder (and the candidate of the check
that a scalar is below `L`, `SD`, after it). -/
abbrev RD (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SR, 64⟩

/-- The registers one word's fold writes. -/
abbrev wordClob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t4]

/-- The registers the engine writes. -/
abbrev engClob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t4, .t5, .t6]

theorem Keeps.toRest {rs : List Reg} {s s' : State} (h : Keeps rs s s') : Rest rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

section
variable {b : Addr}

set_option linter.unusedSimpArgs false in
theorem zero4_ok {s : State} :
    WP isa (.block [.li .a4 0, .li .a5 0, .li .a6 0, .li .a7 0, .li .t4 64]) s fun t =>
      R4 t = 0 ∧ t.gpr .t4 = BitVec.ofNat 64 64 ∧ Keeps [.a4, .a5, .a6, .a7, .t4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show imm12 0 by decide),
    exec_li (show imm12 64 by decide), R4, Word64.val4, RegUpd.gpr_write, reduceCtorEq, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem init_ok {s : State} :
    WP isa (.block scalarInit) s fun t =>
      R4 t = 0 ∧ t.gpr .t4 = BitVec.ofNat 64 64 ∧ t.gpr .t5 = orderLo ∧ t.gpr .t6 = orderHi ∧
      Keeps [.a4, .a5, .a6, .a7, .t4, .t0, .t5, .t6] s t := by
  unfold scalarInit
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono zero4_ok fun s1 ⟨r1, t1, k1⟩ => ?_
  refine WP.mono (Words64.movImm64_ok (by decide) orderLo) fun s2 ⟨g2, o2, m2, d2, w2, p2⟩ => ?_
  refine WP.mono (Words64.movImm64_ok (by decide) orderHi) fun s3 ⟨g3, o3, m3, d3, w3, p3⟩ => ?_
  have k3 : Keeps [.t0, .t5, .t6] s1 s3 :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [o3 r hr.2.2 hr.1, o2 r hr.2.1 hr.1], by rw [m3, m2], by rw [d3, d2], by rw [w3, w2],
      by rw [p3, p2]⟩
  refine ⟨?_, ?_, by rw [o3 _ (by decide) (by decide), g2], g3,
    (k1.trans k3).mono (rs' := [.a4, .a5, .a6, .a7, .t4, .t0, .t5, .t6])⟩
  · rw [← r1]; simp only [R4]
    rw [k3.gpr' (r := .a4), k3.gpr' (r := .a5), k3.gpr' (r := .a6), k3.gpr' (r := .a7)]
  · rw [k3.gpr', t1]

/-- One word: `t4` counted down by 8, the word at `t3 + t4` folded into the remainder. -/
theorem scalarWord_ok {s : State} {p : Addr} (h3 : s.gpr .t3 = p) {k : Nat}
    (h4 : s.gpr .t4 = BitVec.ofNat 64 (8 * (k + 1))) (h5 : s.gpr .t5 = orderLo)
    (h6 : s.gpr .t6 = orderHi) (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8)
    (hr : R4 s < L) :
    WP isa (.block scalarWord) s fun t =>
      R4 t = ((s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * R4 s) % L ∧
      t.gpr .t4 = BitVec.ofNat 64 (8 * k) ∧ Keeps wordClob s t := by
  unfold scalarWord scalarLoad
  simp only [List.cons_append]
  refine wp_subi (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e4 : s1.gpr .t4 = BitVec.ofNat 64 (8 * k) := by
    rw [u1.gpr, h4, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e1 : s2.gpr .a1 = p + BitVec.ofNat 64 (8 * k) := by
    rw [u2.gpr, u1.other _ (by decide), h3, e4]
  refine WP.append (Words64.loadLE64_ok (d := .a2) (tmp := .t0) (tmp2 := .t1) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e1, BitVec.add_zero, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin)) fun s3 u3 => ?_
  have k3 : Keeps [.t4, .a1, .a2, .t0, .t1] s s3 :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u3.other r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2, u2.other r hr.2.1, u1.other r hr.1],
      by rw [u3.mem, u2.mem, u1.mem], by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr],
      by rw [u3.sp, u2.sp, u1.sp]⟩
  have r3 : R4 s3 = R4 s := by
    simp only [R4]
    rw [k3.gpr' (r := .a4), k3.gpr' (r := .a5), k3.gpr' (r := .a6), k3.gpr' (r := .a7)]
  refine WP.mono (wordFold_ok (by rw [k3.gpr', h5]) (by rw [k3.gpr', h6]) (by rw [r3]; exact hr))
    fun t ⟨vt, kt⟩ => ⟨?_, by rw [kt.gpr', u3.other _ (by decide) (by decide) (by decide),
      u2.other _ (by decide), e4], (k3.trans kt).mono (rs' := wordClob)⟩
  rw [vt, r3, u3.gpr, e1, BitVec.add_zero, u2.mem, u1.mem]

/-- The remainder, stored at `SR`. -/
theorem store_ok {s : State} (hc : Ctx b s) :
    WP isa (.block scalarStore) s fun t =>
      V t.mem b SR = R4 s ∧ Rest [] s t ∧ Frame [⟨b + BitVec.ofNat 64 SR, 32⟩] s.mem t.mem := by
  unfold scalarStore
  have hS : SR = 160 := rfl
  refine sd_ok hc (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ⟨by rw [u1.gpr, hc.a3], hc.al, by rw [u1.wr]; exact hc.wr⟩
  refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ⟨by rw [u2.gpr, hc1.a3], hc.al, by rw [u2.wr]; exact hc1.wr⟩
  refine sd_ok hc2 (by omega) (by omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ⟨by rw [u3.gpr, hc2.a3], hc.al, by rw [u3.wr]; exact hc2.wr⟩
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [R64.V_eq4]
    simp only [R64.val4, ew, R4, Word64.val4, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, u2.gpr, u1.gpr, hS,
      Nat.reduceMul, Nat.reduceAdd]
    simp (disch := omega) only [dw_write_self, dw_write_other]
    omega_arith
  · exact ⟨fun r _ => by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr], by rw [u4.rd, u3.rd, u2.rd, u1.rd],
      by rw [u4.wr, u3.wr, u2.wr, u1.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
    simp only [hS, Nat.reduceAdd]
    have hw : ∀ d, 160 ≤ d → d + 8 ≤ 192 → ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m m' →
        ∀ v : BitVec 64, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m (m'.writeW (b + BitVec.ofNat 64 d) v) :=
      fun d h1 h2 _ _ f v => f.writeW (List.mem_singleton_self _) _
        (Offset.contains b h1 (by omega) (by omega))
    exact hw 184 (by omega) (by omega) (hw 176 (by omega) (by omega) (hw 168 (by omega) (by omega)
      (hw 160 (by omega) (by omega) (Frame.refl _ _) _) _) _) _

theorem mod_inner (w a : Nat) : (w + 2 ^ 64 * (a % L)) % L = (w + 2 ^ 64 * a) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- After the words from `n` up: the remainder of the integer they make. -/
structure EngInv (p : Addr) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 8
  keeps : Keeps engClob s0 t
  t4 : t.gpr .t4 = BitVec.ofNat 64 (8 * n)
  t5 : t.gpr .t5 = orderLo
  t6 : t.gpr .t6 = orderHi
  val : R4 t = decodeLE (bytesAt s0.mem (p + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L

/-- **The 64 bytes at `t3`**, modulo `L`, into `SR`. -/
theorem engine_ok {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .t3 = p)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa scalarReduceEngine s fun t =>
      Rest engClob s t ∧ Frame [RD b] s.mem t.mem ∧
      V t.mem b SR = decodeLE (bytesAt s.mem p 64) % L := by
  unfold scalarReduceEngine
  have hS : SR = 160 := rfl
  refine WP.seq (WP.mono init_ok fun s1 ⟨r1, t4, t5, t6, k1⟩ => ?_)
  have i1 : EngInv p s 8 s1 := ⟨Nat.le_refl _, k1.mono (rs' := engClob), t4, t5, t6, by
      rw [r1, show 64 - 8 * 8 = 0 from rfl]; rfl⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (fun n t => 1 ≤ n ∧ EngInv p s n t)
    (Q := fun t => EngInv p s 0 t) ?_ 8 s1 ⟨by decide, i1⟩) fun t ht => ?_)
  · intro n t ⟨hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k < 8 := by have := h.le; omega
    have hr : R4 t < L := by rw [h.val]; exact Nat.mod_lt _ order_pos
    refine WP.mono (scalarWord_ok (p := p) (k := k) (by rw [h.keeps.gpr', h14]) h.t4 h.t5 h.t6
      (by rw [h.keeps.2.2.1, h.keeps.2.2.2.1]; exact hin k hk) hr) fun t' ⟨vt, r4, kt⟩ => ?_
    have hm : t.mem = s.mem := h.keeps.2.1
    have hv : R4 t' = decodeLE (bytesAt s.mem (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [vt, h.val, hm, words_step _ _ _ hk, mod_inner]
    have i' : EngInv p s k t' := ⟨by omega, (h.keeps.trans (kt.mono (rs' := engClob))).mono, r4,
      by rw [kt.gpr', h.t5], by rw [kt.gpr', h.t6], hv⟩
    rw [eval_nonzero, r4]
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by decide, i'⟩
    · have h8 : 8 * k ≠ 0 := by omega
      exact .inr ⟨by rw [ofNat_ne_zero (by omega)]; simp [h8], k, by omega, ⟨by omega, i'⟩⟩
  · refine WP.mono (store_ok (hc.of_rest (Keeps.toRest ht.keeps) (by decide))) fun u ⟨vu, ru, fu⟩ =>
      ⟨(Keeps.toRest ht.keeps).trans (ru.mono (by decide)), ?_, ?_⟩
    · rw [← ht.keeps.2.1]
      exact fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    · rw [vu, ht.val, Nat.mul_zero, Nat.sub_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]

end

end VG.Proof.Ed25519.RISCV64
