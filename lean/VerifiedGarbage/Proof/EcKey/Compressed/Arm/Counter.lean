module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Public loop counters for P-224 coordinate recovery -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem decCounter_ok {j : Nat} (s : State) (hj : 1 ≤ j)
    (hb : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [decCounter]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ Rest [.r11] s t ∧ t.mem = s.mem :=
  wp_decCounter hj hb fun _ u => WP.block_nil ⟨u.gpr, u.rest (by simp), u.mem⟩

theorem testCounter_ok {j : Nat} (s : State) (hj : j < 2 ^ 32)
    (hb : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [testCounter]) s fun t =>
      t.z = decide (j = 0) ∧ Rest [] s t ∧ t.mem = s.mem :=
  wp_testCounter hj hb fun _ f hz => WP.block_nil ⟨hz, f.rest [], f.mem⟩

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 4 ≤ size) (hj : 1 ≤ j) (hj' : j < 2 ^ 32)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.descentCounter c)) s fun t =>
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1) ∧
      t.z = decide (j - 1 = 0) ∧ Rest [.r11] s t ∧
      Outside base (c.sl T2) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.Arm.descentCounter
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hd) fun s₁ u₁ => ?_
  refine wp_decCounter hj (by rw [u₁.gpr, hw]) fun s₂ u₂ => ?_
  have K : Rest [.r11] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest K (by decide)
  refine wp_str (hs₂.off_lt (by omega)) (hs₂.ea (by omega)) (hs₂.write hd) fun s₃ m₃ => ?_
  refine wp_testCounter (j := j - 1) (by omega) (by rw [m₃.gpr, u₂.gpr]) fun t f hz => WP.block_nil ?_
  refine ⟨?_, hz, K.trans ((m₃.rest _).trans (f.rest _)), ?_⟩
  · rw [f.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr]
  · rw [f.mem, m₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.Arm
