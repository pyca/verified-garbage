import VerifiedGarbage.Proof.AesCcm.Arm.B0

/-!
# AES-CCM on ARMv7: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `b0 y` chains `B₀` into a
zeroed MAC state at `W + y` (`b0_ok`); `mac y` then chains the formatted
associated data and the payload padded: CBC-MAC of the formatted blocks
(`mac_ok`), whose first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt format_eq)

section
variable {k w sp : BitVec 32} {R : Nat} (L : Lay k w sp)
include L

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {tl al n : Nat} (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (b0 y) s (MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n])) := by
  refine seq_assoc (WP.seq (WP.mono (b0Pre_ok L he hk etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, hz, hB⟩ => ?_))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok L he₃ hR hy) fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ =>
    ⟨he₄, ?_, ?_, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_mac (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
  · rw [o₄, hz, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w' (by decide)
      · exact L.k_w' (by omega)) hRb]

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s) (hsp₀ : s₀.sp = sp)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {A D : BitVec 32} {tl al n : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hA : Buf w sp s A al) (hD : Buf w sp s D n) :
    WP isa (mac y) s (MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem (State.addr A) al) (bytesAt s.mem (State.addr D) n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (b0_ok L he hk hR etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₁ M₁ => ?_)
  have hk₁ := hk.mac hsp₀ hy16 M₁.frame (by rw [M₁.env.sp, he.sp]) M₁.rd M₁.wr
  refine WP.seq (WP.mono (aad_ok L M₁.env hR hy hk₁ eA eal hal (hA.of_eq M₁.rd M₁.wr)) fun s₂ M₂ => ?_)
  have hk₂ := hk₁.mac hsp₀ hy16 M₂.frame (by rw [M₂.env.sp, M₁.env.sp]) M₂.rd M₂.wr
  obtain ⟨s₃, run₃, h4₃, h5₃, g₃, k₃⟩ := dataLd_ok hk₂ eD en
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := M₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  have rd₃ : s₃.rd = s.rd := by rw [k₃.rd, M₂.rd, M₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [k₃.wr, M₂.wr, M₁.wr]
  refine WP.mono (absorbPad_ok L he₃ hR hy (fun _ => hD.of_eq rd₃ wr₃) hn4 h4₃ h5₃) fun s₄ A₄ => ?_
  have f₂ : Frame (macR w sp y) s.mem s₂.mem := M₁.frame.trans M₂.frame
  have f₃ : Frame (macR w sp y) s.mem s₃.mem := by rw [k₃.mem]; exact f₂
  have hkm := k_macR L hy16
  refine ⟨A₄.env, f₃.trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  rw [A₄.out, k₃.mem, M₂.out, M₁.out, ctxCiph_frame f₂ hkm hRb, ctxCiph_frame M₁.frame hkm hRb,
    buf_kept hD hy16 f₂, buf_kept hA hy16 M₁.frame, format_eq tl hl, length_bytesAt, length_bytesAt,
    Proof.Cmac.chain_append, Proof.Cmac.chain_append]

end

end VG.Proof.AesCcm.Arm
