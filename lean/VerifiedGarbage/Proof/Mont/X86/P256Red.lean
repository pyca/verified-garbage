import VerifiedGarbage.Proof.Mont.X86.SparseShift

/-! # Sparse P-256 reduction on 32-bit x86 -/
namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- Clearing the low word subtracts exactly that word. -/
theorem clearLow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hb : w + 40 ≤ size) :
    WP isa (.block [.mov .eax (.imm 0), .store { base := .ebp, disp := acc } .eax]) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      val32 u.mem base w 10 + w32 s.mem base w = val32 s.mem base w 10 ∧ Keeps [.eax] s u := by
  have hn := hs.nowrap
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  refine wp_storeS (hs₁.ea_at hp₁ (d := acc) (by omega)) (hs₁.write (n := 4) (by omega))
    fun u m => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (off base w) (0 : BitVec 32) := by rw [m.mem, u₁.mem, u₁.gpr, hw]
  have O := writeW32_outside s.mem base (d := w) (0 : BitVec 32) (by omega)
  rw [← hm] at O
  refine ⟨O.mono (Nat.le_refl _) (by omega), ?_, u₁.keeps.trans (m.keeps _)⟩
  change w32 u.mem base w + 2 ^ 32 * val32 u.mem base (w + 4) 9 + _ =
    w32 s.mem base w + 2 ^ 32 * val32 s.mem base (w + 4) 9
  rw [O.val32 (by omega) (by omega), hm, w32_write_self]
  change 0 + _ + _ = _
  omega

theorem p256Red_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hb : w + 40 ≤ size)
    (hq : (s.gpr .ecx).toNat = w32 s.mem base w)
    (hlt : val32 s.mem base w 10 + (s.gpr .ecx).toNat *
      (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) < 2 ^ 320) :
    WP isa (.block (p256Red acc)) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      val32 u.mem base w 10 = val32 s.mem base w 10 + (s.gpr .ecx).toNat *
        (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) ∧ Keeps [.eax] s u := by
  simp only [p256Red, List.append_assoc]
  refine WP.block_append (WP.mono (clearLow_ok hs hp hw hb) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact hp
  refine WP.block_append (WP.mono (positive_ok hs₁ hp₁ hw hb)
    fun s₂ ⟨O₂, ⟨c₂, V₂⟩, K₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp₁
  refine WP.mono (sparseShiftSub_ok hs₂ hp₂ hw (N := 10) (j := 7) (k := 2) rfl hb)
    fun u ⟨O₃, ⟨c₃, V₃⟩, K₃⟩ => ⟨(O₁.trans O₂).trans O₃, ?_, (K₁.trans K₂).trans K₃⟩
  rw [K₁.1 .ecx (by decide)] at V₂
  rw [K₂.1 .ecx (by decide), K₁.1 .ecx (by decide)] at V₃
  have hu := val32_lt u.mem base w 10
  omega

end VG.Proof.Mont.X86
