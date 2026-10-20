module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.Rc4.AArch64.Group

/-! # `vg_mlkem16_cbd2` on AArch64: an iteration, and the loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Cbd16
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (half16 body16 code16 tables constant prepare)

theorem read_input {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < 8)
    (h : Inv s₀ k s) {e : Nat} (he : e < 16) :
    vbyte (s.mem.read (s.gpr .x0) 16) e = BitVec.ofNat 8 (Cbd2.byte s₀ (16 * k + e)) := by
  rw [VG.Proof.Rc4.AArch64.vbyte_read _ _ he, h.x0, ptr_add]
  apply BitVec.eq_of_toNat_eq
  rw [hp.byte_eq h.frame (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (byte_lt _)]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8)
    {s : State} (h : Inv s₀ k s) : WP isa (.block body16) s fun t =>
      Inv s₀ (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  unfold body16
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldrq (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr, h.x0]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  rw [WP.block_append_iff]
  refine WP.mono (prepare_ok s1
    (by rw [h1.get .v18]; exact h.consts.c18)
    (by rw [h1.get .v19]; exact h.consts.c19)
    (by rw [h1.get .v20]; exact h.consts.c20)
    (by rw [h1.get .v21]; exact h.consts.c21)) ?_
  intro s2 ⟨v2, v3, m2, g2, rd2, wr2, sp2, hv2⟩
  have mem2 : s2.mem = s.mem := m2.trans h1.mem
  have gpr2 : s2.gpr = s.gpr := g2.trans h1.gpr
  have cs2 : Consts s2 := h.consts.of fun r r0 r1 r2 r3 _ _ _ _ => by
    rw [hv2 r r0 r1 r2 r3, h1.get r r0]
  have nl : ∀ e < 16,
      (vbyte (VPermOp.eval .zip1 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib s₀ k (16 * 0 + e) ∧
      (vbyte (VPermOp.eval .zip2 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib s₀ k (16 * 1 + e) := by
    intro e he
    rw [v2, v3, h1.v, (byte_zip_nibbles _ he).1, (byte_zip_nibbles _ he).2,
      read_input hp hk h (by omega), read_input hp hk h (by omega)]
    simp only [nib, show 16 * 0 + e = e by omega, show (16 * 1 + e) / 2 = 8 + e / 2 by omega,
      show (16 * 1 + e) % 2 = e % 2 by omega, and_self]
  have hw : s2.wr = [fR s₀] := by rw [wr2, h1.wr, h.wr, hp.wr]
  refine half_ok (c := 0) hk (by decide) rfl hw (by rw [gpr2, h.x1]) cs2 (fun e he => (nl e he).1)
    (by rw [mem2]; exact h.out) (by rw [mem2]; exact h.frame)
    fun s3 g3 rd3 wr3 sp3 hv3 o3 f3 => ?_
  refine half_ok (c := 1) hk (by decide) rfl (by rw [wr3]; exact hw) (by rw [g3, gpr2, h.x1])
    (cs2.of fun r _ _ _ _ r4 r5 r6 r7 => hv3 r r4 r5 r6 r7)
    (fun e he => by
      rw [hv3 .v2 (by decide) (by decide) (by decide) (by decide),
        hv3 .v3 (by decide) (by decide) (by decide) (by decide)]
      exact (nl e he).2)
    o3 f3 fun s4 g4 rd4 wr4 sp4 hv4 o4 f4 => ?_
  have gp4 : s4.gpr = s.gpr := (g4.trans g3).trans gpr2
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 64,
      .subImm .x .x10 .x10 1]) s4 fun t =>
      Only [.x0, .x1, .x10] s4 t ∧
      t.gpr .x0 = s4.gpr .x0 + 16 ∧ t.gpr .x1 = s4.gpr .x1 + 64 ∧
      (t.gpr .x10).toNat = 8 - (k + 1) := by
    refine wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
      wp_subImm (by decide) fun s7 h7 e7 => wp_nil ?_
    refine ⟨((h5.trans h6).trans h7).mono (by decide), ?_, ?_, ?_⟩
    · rw [h7.get .x0, h6.get .x0, e5]; rfl
    · rw [h7.get .x1, e6, h5.get .x1]; rfl
    · rw [e7, toNat_sub_n (by rw [h6.get .x10, h5.get .x10, gp4, h.count]; simp; omega),
        h6.get .x10, h5.get .x10, gp4, h.count]
      simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro s7 ⟨⟨kept, xx0, xx1, cnt⟩, vv⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, cnt, ?_, ?_, ?_⟩, by rw [cnt]; omega⟩
  · rw [kept.rd, rd4, rd3, rd2, h1.rd, h.rd]
  · rw [kept.wr, wr4, wr3, wr2, h1.wr, h.wr]
  · rw [kept.sp, sp4, sp3, sp2, h1.sp, h.sp]
  · rw [xx0, gp4, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]
    congr 2
  · rw [xx1, gp4, h.x1, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ptr_add]
    congr 2
  · exact cs2.of fun r _ _ _ _ r4 r5 r6 r7 => by rw [vv, hv4 r r4 r5 r6 r7, hv3 r r4 r5 r6 r7]
  · rw [kept.mem, show 64 * (k + 1) = 64 * k + 32 * 1 + 32 by omega]; exact o4
  · rw [kept.mem]; exact f4

theorem init (s : State) : WP isa (.block (tables ++ constant .v18 .b16 0x55 ++
    constant .v19 .b16 0x33 ++ constant .v20 .b16 0x22 ++ constant .v21 .b16 15 ++
    ([.movz .x .x10 8 0] : List Instr))) s (Inv s 0) := by
  unfold tables constant
  rrun [List.append_assoc, List.cons_append, List.nil_append, RegUpd.sp_write, RegUpd.sp_setV]
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · change s.gpr .x0 = Cbd2.bP s + BitVec.ofNat 64 (16 * 0)
    simp [Cbd2.bP]
  · change s.gpr .x1 = Cbd2.fP s + BitVec.ofNat 64 (64 * 0)
    simp [Cbd2.fP]
  · exact BytesUpTo.zero _
  · exact Frame.refl _ _

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa code16 s₀ (Inv s₀ 8) := by
  apply WP.seq
  refine WP.mono (init s₀) ?_
  intro s hs
  exact count_loop (by decide) (Inv s₀) (fun k hk t ht => step hp hk ht) hs

end VG.Proof.MlKem.AArch64.Cbd16W
