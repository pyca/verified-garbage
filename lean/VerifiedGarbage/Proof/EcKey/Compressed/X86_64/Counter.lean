module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86_64.Wide

/-! # P-224's descent counter in the scratch buffer -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem loadRbx_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rbx (.mem (sc d))]) s fun s' =>
      s'.gpr .rbx = word s.mem base d ∧ Keeps [.rbx] s s' := by
  exact WP.mono (movMem_ok hs .rbx hd) fun _ ⟨h, _, k⟩ => ⟨h, k⟩

theorem storeRbx_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.store (sc d) .rbx]) s fun s' =>
      word s'.mem base d = s.gpr .rbx ∧ KeepRegs [] s s' ∧
      Outside base d 8 s.mem s'.mem := by
  refine WP.mono (storeReg_ok hs .rbx hd) fun t ⟨hm, _, _, k⟩ => ?_
  refine ⟨?_, k, ?_⟩
  · rw [hm, word_writeW_self]
  · rw [hm]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 8 ≤ size)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.descentCounter c)) s fun s' =>
      word s'.mem base (c.sl T2) = BitVec.ofNat 64 (j - 1) ∧
      s'.zf = some (decide (j - 1 = 0)) ∧
      KeepRegs [.rbx] s s' ∧ Outside base (c.sl T2) 8 s.mem s'.mem := by
  change WP isa (.block ([.mov .rbx (.mem (sc (c.sl T2)))] ++
    ([.alu .sub .rbx (.imm 1)] ++ ([.store (sc (c.sl T2)) .rbx] ++
    [.alu .test .rbx (.reg .rbx)])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadRbx_ok hs hd) fun s₁ ⟨hb₁, k₁⟩ => ?_
  rw [hword] at hb₁
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ hj hj' hb₁) fun s₂ ⟨hb₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeRbx_ok hs₂ hd) fun s₃ ⟨hw₃, k₃, O₃⟩ => ?_
  refine WP.mono (testRbx_ok s₃ (j := j - 1) (by omega) (by rw [k₃.gpr _ (by simp), hb₂])) fun s₄ ⟨hz₄, k₄⟩ => ?_
  refine ⟨by rw [k₄.2.1, hw₃, hb₂], hz₄,
    (((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by simp))).trans
      ((Keeps.regs k₄).mono (by simp)), ?_⟩
  rw [k₄.2.1]
  simpa only [k₂.2.1, k₁.2.1] using O₃

end VG.Proof.EcKey.Compressed.X86_64
