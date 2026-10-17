module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMmul
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the working space's registers

`ctxw_ok` and `ctxW_ok`: from `w` in the division's header and the base in
`r8`, the working space read with `w` or `W` words (`Ws`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem Bs.rS_mem {P : RP} {σ s : State} (h : Bs P σ s) : P.rS ∈ s.wr := by
  rw [h.wr, h.pre.wr]; simp

/-- `ldr r9, [r8, #16]`: `w`. -/
theorem ldrW_ok {P : RP} {σ s : State} (h : Bs P σ s) (r8 : s.gpr .r8 = P.B)
    (cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .r9 (BitVec.ofNat 32 P.w) → WP isa (.block rest) t Q) :
    WP isa (.block (.ldr .r9 .r8 16 :: rest)) s Q := by
  have sz := h.pre.sizes
  have hf := h.pre.fS
  have hz := hdr_Z sz
  refine wp_ldr (by decide) (by rw [r8]; exact addr_add (by simp only [hdr] at hz; omega))
    ⟨P.rS, List.mem_append_right _ h.rS_mem, Offset.contains_base _ (by simp only [hdr] at hz; omega)
      (by decide)⟩ fun t u => k t (by rw [← cnt]; exact u)

theorem ctxw_ok {P : RP} {σ s : State} (h : Bs P σ s) (r8 : s.gpr .r8 = P.B)
    (cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w) :
    WP isa (.block ctxw) s fun t => Ws t P.B P.Z P.w nArr ∧ Rest [.r9, .r7] s t ∧ t.mem = s.mem := by
  have sz := h.pre.sizes
  unfold ctxw
  refine ldrW_ok h r8 cnt fun s1 u1 => ?_
  rw [← List.append_nil stride]
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by have := sz.wle; omega) u1.gpr fun t h7 r m => WP.block_nil ?_
  have rt : Rest [.r9, .r7] s t := (u1.rest (by simp)).trans (r.mono (by simp))
  refine ⟨⟨h.pre.fS, by rw [rt.wr]; exact h.rS_mem, sz.fits, by show 0 < 2 * P.w6 + 2; omega,
    by have := sz.wle; omega, h7,
    by rw [rt.gpr _ (by decide), r8], by rw [r.gpr _ (by decide), u1.gpr]⟩, rt, m.trans u1.mem⟩

theorem ctxW_ok {P : RP} {σ s : State} (h : Bs P σ s) (r8 : s.gpr .r8 = P.B)
    (cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w) :
    WP isa (.block ctxW) s fun t => Ws t P.B P.Z P.W 22 ∧ Rest [.r9, .r7] s t ∧ t.mem = s.mem := by
  have sz := h.pre.sizes
  have wl := sz.wle
  unfold ctxW
  refine ldrW_ok h r8 cnt fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u3.gpr, dpVal, u2.gpr, u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega
  rw [← List.append_nil stride]
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by have := sz.Wle; omega) e9 fun t h7 r m => WP.block_nil ?_
  have rt : Rest [.r9, .r7] s t :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (r.mono (by simp))))
  refine ⟨⟨h.pre.fS, by rw [rt.wr]; exact h.rS_mem, by rw [arrW_end]; exact sz.fits, by show 0 < 2 * P.w + 2; omega,
    by have := sz.Wle; omega, h7, by rw [rt.gpr _ (by decide), r8], by rw [r.gpr _ (by decide), e9]⟩, rt,
    m.trans (u3.mem.trans (u2.mem.trans u1.mem))⟩

end VG.Proof.Rsa.Arm.Recover
