module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! Copies through the joint table's public entry pointer. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem word_at_offset (m : Mem) (base : Addr) (a b : Nat) :
    word m (off base a) b = word m base (a+b) := by
  unfold word off
  rw [VG.Offset.add_add]

theorem source_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    Ptr s .x16 (off base a) (size-a) where
  reg := hr
  enc := by have := hs.enc; omega
  ld d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩

/-- The selected entry is above or wholly below the destination. -/
theorem copyFrom_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a src dst : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    dst + 8*n ≤ size → a + src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (dst + 8*n ≤ a + src ∨ a + src + 8*n ≤ dst) →
    WP isa (.block (copyFrom n dst src)) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base (a+src) n ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, src, dst, hs, hr, hd, ha, hd8, hs8, hsep => by
    have hn := hs.nowrap
    have hp := source_ptr hs (by omega : a ≤ size) hr
    rw [copyFrom,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d:=src) (by omega) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    rw [word_at_offset] at e₀
    have hs₀ := hs.of_keeps k₀ (by decide)
    refine WP.mono (st_out hs₀ (o:=dst) (by omega) hd8 .x4) fun s₁ ⟨m₁,k₁,g₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    have k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    have hs₁ := hs.of_keepRegs k₀₁ (by decide)
    have O₁ : Outside base dst 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    have hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    have e₁ : wordsVal s₁.mem base (a+src+8) n = wordsVal s.mem base (a+src+8) n :=
      O₁.wordsVal (by omega) (by omega)
    refine WP.mono (copyFrom_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega),O₁ x (by omega)]⟩
    rw [show a+(src+8)=a+src+8 by omega] at e₂
    rw [wordsVal,O₂.word (by omega) (by omega),m₁,word_writeW_self,e₂,e₁,wordsVal]
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
