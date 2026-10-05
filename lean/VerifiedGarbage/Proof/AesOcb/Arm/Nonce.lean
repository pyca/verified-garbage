import VerifiedGarbage.Proof.AesOcb.Arm.Offset0
import VerifiedGarbage.Proof.AesOcb.Arm.Calls

/-!
# AES-OCB on ARMv7: `Offset_0` (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers it in
place (`encOne_ok`) into `Ktop`, and takes `Offset_0` from `Stretch`
(`offset0_ok`): §4.2's `Offset_0` (`Proof.Ocb.offset0_eq`), at `W + ofsO` and
`W + o0O` (`nonce_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What `nonce` writes. -/
abbrev nonceR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o0O, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP]

/-- What `nonce` leaves, from `t`. -/
structure NonceOut (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (nonceR p) t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)
  o0 : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)

theorem nonce_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (h4 : t.gpr .r4 = p.N) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonce t (NonceOut p t) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E A h4 h5) fun t₁ N₁ => ?_)
  have E₁ : Env p t₁ := E.of_others N₁.gpr N₁.sp N₁.rd N₁.wr
  refine WP.seq (WP.mono (encOne_ok L E₁ (d := tmpO) (by decide) (by decide)) fun t₂ C₂ => ?_)
  have E₂ := C₂.env E₁
  -- `bottom`, kept through the call
  have hv : ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat < 64 :=
    BitVec.isLt _
  have hbot : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 botO) 32 =
      BitVec.ofNat 32 ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat := by
    rw [C₂.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide), N₁.bot]
  obtain ⟨t₃, run₃, O₃⟩ := offset0_ok L E₂ hv hbot
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  have hK : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      Spec.Ocb.aesWith p.R (sched p t.mem) (Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl) &&&
        ~~~(63 : Block)) := by
    have := C₂.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, encF_ciph, N₁.blk]
    refine congrArg (fun w => Spec.Ocb.aesWith p.R w _) ?_
    exact Proof.Cmac.bytesAt_frame N₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.k_w' (d := tmpO) (k := 16) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega))
      · exact (L.k_w' (d := botO) (k := 4) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)
  have hO : (stretch (blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb'
      (64 - ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat) 128 =
      Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl) := by
    rw [hK, Proof.Ocb.offset0_eq]; rfl
  refine ⟨E₂.of_others O₃.gpr O₃.sp O₃.rd O₃.wr, by rw [O₃.rd, C₂.rd, N₁.rd], by rw [O₃.wr, C₂.wr, N₁.wr], ?_,
    by rw [O₃.ofs, hO], by rw [O₃.o0, hO]⟩
  exact ((N₁.frame.mono (by simp)).trans (C₂.frame.mono (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [tmpO]))).trans (O₃.frame.mono (by simp))

end VG.Proof.AesOcb.Arm
