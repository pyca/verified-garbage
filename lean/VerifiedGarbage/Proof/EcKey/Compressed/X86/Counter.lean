module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Public loop counters for P-224 coordinate recovery -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem decCounter_ok {j : Nat} (s : State) (hj : 1 ≤ j)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [decCounter]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j - 1) ∧ Keeps [.esi] s t ∧ t.mem = s.mem :=
  wp_decCounter hj hb fun _ hb K hm => WP.block_nil ⟨hb, K, hm⟩

theorem testCounter_ok {j : Nat} (s : State) (hj : j < 2 ^ 32)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [testCounter]) s fun t =>
      t.zf = some (decide (j = 0)) ∧ Keeps [] s t ∧ t.mem = s.mem :=
  wp_testCounter hj hb fun _ f hz => WP.block_nil ⟨hz, ⟨fun r _ => congrFun f.gpr r, f.rd, f.wr⟩, f.mem⟩

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 4 ≤ size) (hj : 1 ≤ j) (hj' : j < 2 ^ 32)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (.block (Impl.EcKey.Compressed.X86.descentCounter c)) s fun t =>
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1) ∧
      t.zf = some (decide (j - 1 = 0)) ∧ Keeps [.esi] s t ∧
      Outside base (c.sl T2) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.X86.descentCounter
  refine wp_movS (show readSrc s (.mem (Impl.Mont.X86.sc (c.sl T2))) = some (s.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs.ea (d := c.sl T2) (by omega), hs.read hd, ite_true]) fun s₁ u₁ _ => ?_
  refine wp_decCounter hj (by rw [u₁.gpr, hw]) fun s₂ hb₂ k₂ m₂ => ?_
  have K : Keeps [.esi] s s₂ := u₁.keeps.trans k₂
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hd) fun s₃ m₃ => ?_
  refine wp_testCounter (j := j - 1) (by omega) (by rw [m₃.gpr, hb₂]) fun t f hz => WP.block_nil ?_
  refine ⟨?_, hz, K.trans ((m₃.keeps _).trans ⟨fun r _ => congrFun f.gpr r, f.rd, f.wr⟩), ?_⟩
  · rw [f.mem, m₃.mem, Mem.readW_writeW_self32, hb₂]
  · rw [f.mem, m₃.mem, m₂, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86
