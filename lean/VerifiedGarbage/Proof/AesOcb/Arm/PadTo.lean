import VerifiedGarbage.Proof.AesOcb.Arm.NonceBlock

/-!
# AES-OCB on ARMv7: `pad(S)` (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes
`pad(S) = S ‖ 1 ‖ zeros` (§4.1), for the `n` bytes `S` at `r4`
(`0 < n < 16`), to `W + d`: zeros, the bytes copied (`copyLoop`), and `0x80`
after them (`padTo_ok`), as on AArch64 (`Proof.AesOcb.AArch64.padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre mem_store gpr_store rd_store wr_store sp_store)

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.r0, .r1, .r2, .r3, .r12]

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `r4`, `0 < n < 16`. -/
theorem padTo_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {S : BitVec 32} {n d : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (he : encodable (BitVec.ofNat 32 d) = true)
    (h4 : s.gpr .r4 = S) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (fS : S.toNat + n ≤ 2 ^ 32)
    (hS : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) = pad (bytesAt s.mem (State.addr S) n) ∧
      Others padRegs s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  unfold padTo
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (s := s) (o := d) (by omega) (by rw [E.r11]; omega)
    (by rw [E.r11]; exact E.perm.wC hd)) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  have r4₁ : s₁.gpr .r4 = S := by rw [R₁.gpr _ (by decide), h4]
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [R₁.gpr _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [he, r11₁, r4₁, r5₁], ?_⟩
  have eS : bytesAt s₁.mem (State.addr S) n = bytesAt s.mem (State.addr S) n := by
    rw [R₁.mem]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  refine WP.seq (WP.mono (copyLoop_ok _ (S := S) (D := p.W + BitVec.ofNat 32 d) (n := n)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], hn, by omega, fS,
      by rw [L.wN (by omega)]; omega, by simp only [rd_setReg, wr_setReg, R₁.rd, R₁.wr]; exact hS,
      by simp only [wr_setReg, R₁.wr, ed]; exact Proof.AesGcm.Arm.covers_prefix (E.perm.wC hd) (by omega),
      by rw [ed]; exact hSD.sub_right (Region.sub_prefix (by omega))⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_setReg, ed] at m₃
  rw [eS] at m₃
  have edn : State.addr (p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add, L.wA (by omega), Offset.add_add]
  have w₃ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [O₃.wr]; simp only [wr_setReg, R₁.wr, Offset.add_add]; exact E.perm.wW (d := d + n) (n := 1) (by omega)
  refine WP.of_runBlock ⟨_, by orun [O₃.r2, edn, w₃], ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (State.addr p.W + BitVec.ofNat 64 d)
      (bytesAt s.mem (State.addr S) n)).writeW (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b =
      writeBytes m (State.addr p.W + BitVec.ofNat 64 d) (bytesAt s.mem (State.addr S) n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, mem_setReg]
    rw [m₃, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega)) x hx]
    have F1 : Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem s₁.mem := by
      rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    exact F1 x hx
  · simp only [mem_store, mem_setReg]
    rw [m₃, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₁]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
    rfl
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, ite_false]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_setReg, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; rw [O₃.rd]; simp [rd_setReg, R₁.rd]
  · simp only [wr_store, wr_setReg]; rw [O₃.wr]; simp [wr_setReg, R₁.wr]

end VG.Proof.AesOcb.Arm
