import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideChain

/-! Closing a sixteen-word chain and advancing its public counter. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem carry_bound {R V T X Y C H : Nat} (hR : 0 < R) (hT : T < R)
    (hX : X < 2 ^ 64) (hY : Y < R) (hC : C < 2 ^ 64)
    (he : V + R * H = T + X * Y + C) : H < 2 ^ 64 := by
  have hp : X * Y ≤ (2 ^ 64 - 1) * (R - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hb : R * H < R * 2 ^ 64 := by omega_using [he, hp, hR, hT, hC]
  exact Nat.lt_of_mul_lt_mul_left hb

theorem block_ok {s : State} {B : Addr} {Z e eb j w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 128 ≤ Z) (hZb : eb + 8 * j + 128 ≤ Z)
    (sb : eb + 8 * j + 128 ≤ e + 8 * j ∨ e + 8 * j + 128 ≤ eb + 8 * j)
    (hj : j + 16 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquareWide.block) s fun t =>
      wv t.mem B (e + 8 * j) 16 + 2 ^ 1024 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 16 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 16 + (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 128 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ Keep [.rsi, .rax, .r11, .rcx, .r14] s t := by
  unfold AdxSquareWide.block
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun a ⟨_, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok 8 (k := 0) (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by simpa using hZ) (by simpa using hZb) (by simpa using sb) ca oa)
    fun b ⟨cb, ob, hcb, hob, eq, out, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Bool.toNat_false, ka.2.1] at eq out
  rw [ka.gpr (r := .rdx) (by decide), ka.gpr (r := .rcx) (by decide)] at eq
  rw [WP.block_append_iff]
  refine WP.mono (close_ok b hcb hob (by decide)) fun d ⟨cd, od, _, _, ed, kd⟩ => ?_
  have hT := wv_lt s.mem B (e + 8 * j) 16
  have hB := wv_lt s.mem B (eb + 8 * j) 16
  simp only [Nat.reduceMul] at hT hB
  have hX := (s.gpr .rdx).isLt
  have hC := (s.gpr .rcx).isLt
  have hb : (b.gpr .rcx).toNat + cb.toNat + ob.toNat < 2 ^ 64 :=
    carry_bound (R := 2 ^ 1024) (V := wv b.mem B (e + 8 * j) 16)
      (T := wv s.mem B (e + 8 * j) 16) (X := (s.gpr .rdx).toNat)
      (Y := wv s.mem B (eb + 8 * j) 16) (C := (s.gpr .rcx).toNat)
      (Nat.two_pow_pos 1024) hT hX hB hC eq
  have eclose : (d.gpr .rcx).toNat = (b.gpr .rcx).toNat + cb.toNat + ob.toNat := by
    have := Bool.toNat_le cd; have := Bool.toNat_le od
    omega_using [ed, hb, this]
  have k := (ka.keep.trans kb).trans kd.keep
  have h14d := (k.gpr (by decide)).trans h14
  have hbxd := (k.gpr (by decide)).trans hbx
  have tail : WP isa (.block [.alu .add .r14 (.imm 16), .alu .cmp .r14 (.reg .rbx)]) d fun t =>
      t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧ t.zf = some (decide (j + 16 = w)) ∧
      t.mem = d.mem ∧ Keep [.r14] d t := by
    refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ t.mem = d.mem) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
    have ha : BitVec.ofNat 64 j + 16 = BitVec.ofNat 64 (j + 16) := by
      rw [BitVec.ofNat_add]; rfl
    xrun [h14d, hbxd, ha, ofNat_sub_beq hj hw]
  refine WP.mono tail fun t ⟨ht14, htz, hm, kt⟩ => ⟨?_, ?_, ht14, htz, (k.trans kt).mono (by simp)⟩
  · rw [hm, kd.2.1, kt.gpr (by decide), eclose]; exact eq
  · rw [hm, kd.2.1]; exact out
end VG.Proof.Bignum.X86_64.AdxSquareWide
