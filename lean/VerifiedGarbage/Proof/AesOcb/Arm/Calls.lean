import VerifiedGarbage.Proof.AesOcb.Arm.Words
import VerifiedGarbage.Proof.Ocb.State

/-!
# AES-OCB on ARMv7: the calls

Untrusted: everything here is checked by Lean. A call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on `n` blocks at `D`, with
the key context's schedule and the working space at `W + scrO`
(`blkFrame_ok`): each block is replaced with the cipher (`BlkFn.ciph`) of
it, for the key schedule in the key context, and the registers `r4`–`r11`
are kept (`CallPost`). `encOne d` enciphers the block at `W + d`
(`encOne_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- The registers the calls keep. -/
abbrev keptRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- `F` as a blockcipher on OCB's blocks. -/
def BlkFn.ciph (F : BlkFn) (R : Nat) (w : List Byte) : Spec.Ocb.Cipher := fun x =>
  Spec.Ocb.ofBytes (F.f R w (Vector.ofFn fun i => (Spec.Ocb.toBytes x).getD i.1 0)).toList

theorem encF_ciph (R : Nat) (w : List Byte) : encF.ciph R w = Spec.Ocb.aesWith R w := rfl
theorem decF_ciph (R : Nat) (w : List Byte) : decF.ciph R w = Spec.Ocb.aesInvWith R w := rfl

/-- The key schedule in the memory `m`, for `R` rounds. -/
abbrev sched (p : Prm) (m : Mem) : List Byte := bytesAt m (State.addr p.K) (16 * (p.R + 1))

/-- What a call leaves, from `t`. -/
structure CallPost (F : BlkFn) (p : Prm) (D : Addr) (n : Nat) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  saved : ∀ r ∈ keptRegs, t'.gpr r = t.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  out : ∀ i < n, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * i)) =
    F.ciph p.R (sched p t.mem) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)))

theorem CallPost.env {F : BlkFn} {p : Prm} {D : Addr} {n : Nat} {t t' : State} (h : CallPost F p D n t t')
    (E : Env p t) : Env p t' :=
  E.keep (fun r hr => h.saved r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    h.sp h.rd h.wr

/-- The arguments of a call, set up. -/
theorem blkCall_of {p : Prm} (L : Lay p) {t : State} (E : Env p t) {D : BitVec 32} {n : Nat}
    (h0 : t.gpr .r0 = p.K) (h1 : t.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : t.gpr .r2 = D)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 n) (h12 : t.gpr .r12 = p.W + BitVec.ofNat 32 scrO)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (wD : Covers [⟨State.addr D, 16 * n⟩] t.wr)
    (dk : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩)
    (db : (below p.SP).Disjoint ⟨State.addr D, 16 * n⟩) :
    BlkCall t p.K D (p.W + BitVec.ofNat 32 scrO) p.R n := by
  have fw := L.ww
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  exact {
    r0 := h0, r1 := h1, r2 := h2, r3 := h3, r12 := h12, rounds := L.rounds
    hsp := by rw [E.sp]; exact L.sp8
    fitK := by have := L.kw; omega
    fitD := fD
    fitS := by rw [L.wN (by decide)]; simp only [scrO]; omega
    kd := dk.sub_left (Region.sub_prefix (by decide))
    ks := by rw [eS]; exact (L.k_w' (by decide)).sub_left (Region.sub_prefix (by decide))
    ds := by rw [eS]; exact ds
    bk := by rw [E.sp]; exact L.bk.sub_right (Region.sub_prefix (by decide))
    bd := by rw [E.sp]; exact db
    bs := by rw [E.sp, eS]; exact L.bw' (by decide)
    reads := Proof.AesGcm.Arm.covers_prefix E.perm.k (by decide)
    writes := by
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact wD a k ⟨_, List.mem_singleton_self _, hc⟩
      · rw [eS] at hc; exact E.perm.wC (d := scrO) (n := 2048) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩ }

/-- A call of `F`, set up. -/
theorem blkFrame_ok (F : BlkFn) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {D : BitVec 32} {n : Nat}
    (h0 : t.gpr .r0 = p.K) (h1 : t.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : t.gpr .r2 = D)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 n) (h12 : t.gpr .r12 = p.W + BitVec.ofNat 32 scrO)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (wD : Covers [⟨State.addr D, 16 * n⟩] t.wr)
    (dk : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩)
    (db : (below p.SP).Disjoint ⟨State.addr D, 16 * n⟩) :
    WP isa (blkFrame F) t (CallPost F p (State.addr D) n t) := by
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  have hB := blkCall_of L E h0 h1 h2 h3 h12 fD wD dk ds db
  refine WP.mono (blk_call F hB) fun t' P => ⟨P.rd, P.wr, P.sp, fun r hr => P.saved r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h | h <;> simp [h]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with h | h | h | h | h | h | h | h <;>
        subst h <;> decide), ?_, fun i hi => ?_⟩
  · have f := P.frame; rw [eS, E.sp] at f; exact f
  · rw [Proof.Ocb.blockAtMem_of_state _ (Proof.Ocb.stateAt_of_statesAt P.out hi)]
    rfl

/-- `ENCIPHER` of the block at `W + d`, in place. -/
theorem encOne_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {d : Nat} (hd : d + 16 ≤ 512)
    (he : encodable (BitVec.ofNat 32 d) = true) :
    WP isa (encOne d) t (CallPost encF p (State.addr p.W + BitVec.ofNat 64 d) 1 t) := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [encOne, callArgs, E.r9, E.r10, E.r11, he], ?_⟩)
  have := blkFrame_ok encF L (t := ((((((t.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 (p.W + BitVec.ofNat 32 d)).setReg .r3 (BitVec.ofNat 32 1))))
    (D := p.W + BitVec.ofNat 32 d) (n := 1) (E.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac)
      (by rfl) (by rfl) (by rfl)) (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by omega)]; omega)
      (by rw [ed]; exact E.perm.wC (by omega)) (by rw [ed]; exact L.k_w' (by omega))
      (by rw [ed]; exact L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
      (by rw [ed]; exact L.bw' (by omega))
  rw [ed] at this
  refine WP.mono (encFrame_eq ▸ this) fun t' P => ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [P.rd]; rfl
  · rw [P.wr]; rfl
  · rw [P.sp]; rfl
  · rw [P.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · exact P.frame
  · intro i hi; rw [P.out i hi]; rfl

end VG.Proof.AesOcb.Arm
