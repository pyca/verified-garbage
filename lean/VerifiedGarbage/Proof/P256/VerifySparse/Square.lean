import VerifiedGarbage.Proof.P256.VerifySparse.Correct
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Mont.AArch64.P256Square
open VG.Proof.Ed25519.AArch64 (Keeps)

def sparseSquare (o a : Nat) : List Instr :=
  core a ++ (Impl.P256.VerifySparse.correct [.x8,.x9,.x10,.x11] .x12 ++
    stores [.x8,.x9,.x10,.x11] o)

theorem square_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) (hN : M.n=4) (hM : ModOkA M size p s.mem base) (hA : ModA M)
    {o a : Nat} (ho : o+32 ≤ size) (ha : a+32 ≤ size) (ho8 : o%8=0) (ha8 : a%8=0)
    (hB : wordsVal s.mem base a 4 < p) :
    WP isa (.block (sparseSquare o a)) s fun t => SquareKeep base o s t ∧
      wordsVal t.mem base o 4 < p ∧
      wordsVal t.mem base o 4 * R % p = wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % p := by
  rw [sparseSquare,WP.block_append_iff]
  refine WP.mono (core_ok hs ha ha8) fun s₁ ⟨⟨u,hu,e₁⟩,z₁,k₁⟩ => ?_
  have pe : P256Square.p=p := by decide
  rw [pe] at e₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hb := square_redc_bound hB hu e₁
  have hV : regsVal s₁ [.x8,.x9,.x10,.x11] + 2^(64*M.n)*(s₁.gpr .x12).toNat < 2*p := by
    simpa only [low_regs,hN,pe] using hb
  rw [WP.block_append_iff]
  refine WP.mono (correctP_ok hs₁ (M:=M) hME (ts:=[.x8,.x9,.x10,.x11]) (top:=.x12)
    (by simpa only [List.length_cons,List.length_nil] using hN.symm) hM.n0 hM.n10
    (by unfold Fresh; decide) hM.mo hA.mo z₁ (by rw [k₁.mem]; exact hM.val) hV)
    fun s₂ ⟨e₂,k₂⟩ => ?_
  have hkc : ∀ r ∈ (.x2 :: .x17 :: [.x8,.x9,.x10,.x11] ++ dRegs M.n), r ∈ squareClob := by
    rw [hN]; decide
  have k₂' := k₂.mono hkc
  have hs₂ := hs₁.of_keeps k₂' (by decide)
  refine WP.mono (stores_ok [.x8,.x9,.x10,.x11] hs₂ ho ho8 (by decide))
    fun t ⟨e₃,k₃,o₃⟩ => ?_
  change wordsVal t.mem base o 4 = regsVal s₂ [.x8,.x9,.x10,.x11] at e₃
  have kp := k₁.trans k₂'
  refine ⟨⟨fun r hr => (k₃.gpr r (by simp)).trans (kp.gpr r hr),
    k₃.rd.trans kp.rd,k₃.wr.trans kp.wr,k₃.sp.trans kp.sp,
    fun x hx => (o₃ x hx).trans (congrFun kp.mem x)⟩,?_,?_⟩
  · rw [e₃,e₂]; exact Nat.mod_lt _ (by decide)
  · rw [e₃,e₂,low_regs,hN,Nat.mod_mul_mod,Nat.mul_comm]
    change R*(lowValue s₁+R*(s₁.gpr .x12).toNat)%p = _
    rw [e₁,Nat.add_mul_mod_self_right]


end VG.Proof.P256.VerifySparse
