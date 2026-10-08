import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupOps

/-! # Scratch metadata saved at entry and restored at exit -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64

def metaR (s : State) : Region := ⟨s.gpr .r11 + BitVec.ofNat 64 768, 48⟩

theorem meta_frame (s : State) : Frame [metaR s] s.mem (metaMem s) := by
  unfold metaMem
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_).writeW
    List.mem_cons_self _ ?_ |>.writeW List.mem_cons_self _ ?_
  · exact Offset.contains (s.gpr .r11) (d := 768) (n := 16) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 784) (n := 16) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 808) (n := 8) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 800) (n := 8) (e := 768) (k := 48) (by decide) (by decide) (by decide)

theorem meta_mask (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 = s.lane .xmm0 0 := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 808) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 784) (k := 16) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self s.mem _ 16 _ (by decide)]

theorem meta_poly (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 784) 128 = s.lane .xmm1 0 := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 784) (n := 16) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 784) (n := 16) (e := 808) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self _ _ 16 _ (by decide)]

theorem meta_rounds (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 800) 64 = s.gpr .rsi := by
  rw [metaMem, Mem.readW_writeW_self64]

theorem meta_data (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 808) 64 = s.gpr .rdx := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 808) (n := 8) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

end VG.Proof.Gcm.X86_64.StitchAvx8
