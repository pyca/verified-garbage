module

public import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Encode the SEC 1 parity tag on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86 VG.Impl.Ecdsa.X86
open VG.Proof.EcKey.X86 (wp_store8S)

theorem tag32_byte (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) (b : Bool) :
    ((((m.readW (off base a) 32 &&& 1) ||| 2) &&& mask32 (b = true)).setWidth 8) =
      if b then BitVec.ofNat 8 (2 + wordsVal m base a n % 2) else 0 := by
  rw [word32_parity m base a n hn]
  rcases Nat.mod_two_eq_zero_or_one (wordsVal m base a n) with h | h <;>
    cases b <;> simp [h, mask32] <;> decide

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86.QY + 4 ≤ size) {o : BitVec 32}
    (hout : s.gpr .ebx = o) (hw : InRegions s.wr (o.setWidth 64) 1) (b : Bool)
    (hf : s.gpr .ecx = mask32 (b = true)) (hn : 0 < c.n) :
    WP isa (.block (Impl.EcKey.Compressed.X86.compressTag c)) s fun t =>
      t.mem (o.setWidth 64) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0) ∧
      Outside (o.setWidth 64) 0 1 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold Impl.EcKey.Compressed.X86.compressTag
  refine wp_movS (readSrc_sc hs hy) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_orS rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have K : Keeps [.eax] s s₄ := u₁.keeps.trans (u₂.keeps.trans (u₃.keeps.trans u₄.keeps))
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ho : s₄.gpr .ebx = o := (K.1 _ (by decide)).trans hout
  have ht : (s₄.gpr .eax).setWidth 8 =
      if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0 := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide), hf]
    exact tag32_byte _ _ _ _ hn b
  refine wp_store8S (a := o.setWidth 64) (by change addr (s₄.gpr .ebx) 0 = _; rw [ho]; simp [addr])
    (by rw [K.2.2]; exact hw) fun t mt => WP.block_nil ?_
  refine ⟨?_, ?_, K.trans (mt.keeps _)⟩
  · rw [mt.mem, writeW8_self]
    simpa only [Reg8.reg] using ht
  · rw [mt.mem, ← hm]
    simpa [off, Reg8.reg] using (writeW8_outside s₄.mem (o.setWidth 64) (d := 0) ((s₄.gpr .eax).setWidth 8) (by decide))

end VG.Proof.EcKey.Compressed.X86
