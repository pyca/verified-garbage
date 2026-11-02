module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Bits
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: `e`

`loadE_ok`: `e`'s `e_len` octets, most significant first, from the frame's
`oE` and `oELen` into `s10`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Mont (off)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (loadE ldf oE oELen)

/-- `e`'s value. -/
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat)

theorem os2ip_bytes_lt (m : Mem) (E : Addr) : ∀ i, Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E i) < 256 ^ i
  | 0 => by simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
  | i + 1 => by
    rw [Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, Nat.pow_succ]
    have := os2ip_bytes_lt m E i
    have := (m (off E i)).isLt
    omega_arith

theorem eV_lt {s0 : State} (hp : CIn s0) : eV s0 < 2 ^ 64 := by
  have h1 := os2ip_bytes_lt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat
  have h8 : (256 : Nat) ^ (s0.gpr .a4).toNat ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hp.el2
  have h9 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  simp only [eV]
  omega_arith

theorem read_byte (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Proof.Mont.read_toNat_succ]
  simp [Mem.read]

/-- `loadE`: `e` into `s10`. -/
theorem loadE_ok {s0 s : State} (h : Fr s0 s) :
    WP isa loadE s fun t =>
      (t.gpr .s10 = BitVec.ofNat 64 (eV s0) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .t4, .t5, .s10] s t := by
  have hp := h.pre
  generalize hE : s0.gpr .a3 = E
  generalize hL : (s0.gpr .a4).toNat = L
  have hL1 : 1 ≤ L := hL ▸ hp.el1
  have hL8 : L ≤ 8 := hL ▸ hp.el2
  have eL : s0.gpr .a4 = BitVec.ofNat 64 L := by rw [← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hfe : E.toNat + L ≤ 2 ^ 64 := by rw [← hE, ← hL]; exact hp.fe
  have hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off E i) 1 := fun i hi =>
    ⟨cE s0, List.mem_append_left _ (by rw [h.rd]; exact hp.rE), by
      show (⟨s0.gpr .a3, (s0.gpr .a4).toNat⟩ : Region).Contains _ _
      rw [hE, hL]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hbytes : Spec.Rsa.bytesAt s.mem E L = Spec.Rsa.bytesAt s0.mem E L := by
    refine bytes_keep h.out (by omega_arith) fun ρ hρ => ?_
    have e : (⟨E, L⟩ : Region) = cE s0 := by rw [← hE, ← hL]
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hp.oE.symm
    · exact hp.uE.symm
    · exact hp.eS
    · exact hp.Fe.symm
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r128 : s.mem.readW (fb s0 + BitVec.ofNat 64 128) 64 = E := hE ▸ h.wE
  have r136 : s.mem.readW (fb s0 + BitVec.ofNat 64 136) 64 = BitVec.ofNat 64 L := eL ▸ h.wELen
  unfold loadE
  refine WP.seq ?_
  have hpre : WP isa (.block [.li .t2 0, ldf .t3 oE, ldf .t5 oELen]) s fun s₁ =>
      (s₁.gpr .t2 = 0 ∧ s₁.gpr .t3 = off E 0 ∧ s₁.gpr .t5 = BitVec.ofNat 64 L ∧ s₁.mem = s.mem) ∧
        Keep [.t2, .t3, .t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ldf, oE, oELen, h.s11, al 128 (by decide), al 136 (by decide), inr 128 (by decide),
      inr 136 (by decide), r128, r136, fin64_exec_li_zero]
    exact (BitVec.add_zero _).symm
  refine WP.mono hpre fun s₁ ⟨⟨i2, i3, i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t2 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i)) ∧
      t.gpr .t3 = off E i ∧ t.mem = s.mem ∧ Keep [.t2, .t3, .t4, .t5] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t2, t3, tm, tk⟩ _ => ?_)
    ⟨by rw [i2]; rfl, i3, im, k₁.mono (by decide)⟩ i5) fun t ⟨t2, _, tm, tk⟩ => ?_)
  · have hb : InRegions (t.rd ++ t.wr) (off E i) 1 := by rw [tk.2.1, tk.2.2]; exact hrd i hi
    refine WP.mono (WP.keep [.t2, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t2 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E (i + 1))) ∧
        t'.gpr .t3 = off E (i + 1) ∧ t'.mem = t.mem ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl)
        (by rfl))
      fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c.trans tm, Keep.trans' tk k⟩, d⟩
    brun [t3, t2, hb, read_byte]
    apply BitVec.eq_of_toNat_eq
    rw [Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, tm, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hbt := (s.mem (off E i)).isLt
    have hlt := os2ip_bytes_lt s.mem E i
    have h256 : 256 ^ i ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
    rw [Nat.mod_eq_of_lt (show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i) < 2 ^ 64 by omega_arith)]
    omega_arith
  · have hfin : WP isa (.block [.addi .s10 .t2 0]) t fun t' =>
        (t'.gpr .s10 = t.gpr .t2 ∧ t'.mem = t.mem) ∧ Keep [.s10] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun
      exact BitVec.add_zero _
    refine WP.mono hfin fun t' ⟨⟨a, b⟩, k⟩ => ⟨⟨?_, b.trans tm⟩, Keep.trans' (tk.mono (by decide)) (k.mono (by decide))⟩
    rw [a, t2, hbytes, ← hE, ← hL]

end VG.Proof.RsaKeyGen.RISCV64.Cand
