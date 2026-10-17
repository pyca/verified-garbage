module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: reading a number into an array (`load_ok'`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `load j`: array `j`'s `w + 2` words := the `k` bytes at `r4` (`r6 = k`). -/
theorem load_ok' {P : RP} {σ s : State} (h : Bs P σ s) (hw : Ws s P.B P.Z P.w nArr) {j : Nat}
    (hj : j < nArr) {src : BitVec 32} {k : Nat}
    (rd : InRegions (σ.rd ++ σ.wr) (State.addr src) k) (sepS : Region.Disjoint ⟨State.addr src, k⟩ P.rS)
    (sepF : Region.Disjoint ⟨State.addr src, k⟩ P.rFr) (fit : src.toNat + k ≤ 2 ^ 32) (hk : 0 < k)
    (hkK : k ≤ P.K) (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (VG.Impl.Rsa.Arm.CrtValues.load j) s fun t => Bs P σ t ∧ Ws t P.B P.Z P.w nArr ∧
      Keep P.B P.w [j] [] s.mem t.mem ∧
      val32 t.mem (State.addr P.B) (arr P.w j) (P.w + 2) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have sz := h.pre.sizes
  have fa := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S P.w = 4 * (P.w + 2) := rfl
  have hkw : k ≤ 4 * P.w := by have := sz.kw; omega
  rw [VG.Impl.Rsa.Arm.CrtValues.load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have bu := h.of_rest rest mu
  have hu := hw.rest rest
  have ad : State.addr (P.B + BitVec.ofNat 32 (arr P.w j)) = off (State.addr P.B) (arr P.w j) :=
    hw.addr (by omega)
  have p0 : u.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.w j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := P.B + BitVec.ofNat 32 (arr P.w j)) (n := P.w + 2)
    hk (by omega) (by omega) fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega)
    (by rw [bu.rd, bu.wr]; exact rd)
    ⟨P.rS, by rw [bu.wr]; exact h.rS_mem |> fun m => by rw [h.wr] at m; exact m,
      by rw [ad]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by
      rw [ad]
      refine fun a ha hb => sepS a ha ?_
      exact Region.Contains.byte (r := P.rS) (b := off (State.addr P.B) (arr P.w j)) (n := 4 * (P.w + 2))
        (Offset.contains_base _ (by omega) (by omega)) (by simp only [Region.Contains] at hb; omega))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9]
        exact (BitVec.ofNat_add_ofNat (n := 32) P.w 2))
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  have k : Keep P.B P.w [j] [] u.mem t.mem := VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr f (by omega)
  refine ⟨bu.of_frame (k.frameS (by simpa using fitZ_w sz hj) (by simp) (hdr_Z sz)) r.sp r.rd r.wr,
    hu.rest r, mu ▸ k, ?_, (rest.mono (by simp)).trans (r.mono (by simp))⟩
  rw [VG.Proof.Rsa.Arm.CrtValues.val32_off, Nat.add_zero] at v
  rw [v, mu, VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sepS
    · exact sepF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 56) (by decide)) |>
        fun d => by simpa using d) (by omega)]

end VG.Proof.Rsa.Arm.Recover
