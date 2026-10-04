import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
import VerifiedGarbage.Proof.Ocb.Bytes

/-!
# AES-OCB on AArch64: padding a string (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `x23` to `W + d`: zeros, the bytes
(AES-GCM's `copyLoop`), and `0x80` after them (`padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok LoopPre in_left in_off)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a (v : Byte) := by
  simp [Mem.writeW]

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← toBytes_zero, ← h]; rfl

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.x9, .x11, .x12, .x13, .x14, .x15]

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `x23`, `0 < n < 16`. -/
theorem padTo_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 8 = 0 ∧ d + 16 ≤ 2560) (h23 : s.gpr .x23 = S)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 d) = pad (bytesAt s.mem S n) ∧
      (∀ r, r ∉ padRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := d) ⟨hd.1, by omega⟩ h19 (wW (by omega)) (wW (by omega))
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 d, Impl.AesGcm.AArch64.mov .x12 .x23,
        Impl.AesGcm.AArch64.mov .x13 .x24] s₁ = some s₂ ∧
      s₂.gpr .x11 = W + BitVec.ofNat 64 d ∧ s₂.gpr .x12 = S ∧ s₂.gpr .x13 = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
    have h23₁ : s₁.gpr .x23 = S := by rw [B₁.gpr _ (by decide), h23]
    have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 n := by rw [B₁.gpr _ (by decide), h24]
    refine ⟨_, by orun [show d < 4096 by omega], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h19₁]
    · simp [gpr_write, h23₁]
    · simp [gpr_write, h24₁]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact Proof.AesGcm.AArch64.covers_off hw (by omega) (by decide)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.Cmac.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ hn ⟨by omega, hS₂, hD₂, hSD'⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, x11₃, g₃, sp₃, rd₃, wr₃⟩ := h₃
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact wW (by omega)
  refine WP.of_runBlock ⟨_, by orun [x11₃, w₃, write1], ?_⟩
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b = writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, by rw [sp₃, sp₂, B₁.sp], by rw [rd₃, rd₂, B₁.rd], by rw [wr₃, wr₂, B₁.wr]⟩
  · dsimp only
    rw [m₃, eS, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · dsimp only
    rw [m₃, eS, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
    rfl
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    dsimp only
    rw [gpr_write_of_ne _ _ _ hr.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      g₂ r hr.2.1 hr.2.2.1 hr.2.2.2.1, B₁.gpr r (by simp [hr.1])]

end VG.Proof.AesOcb.AArch64
