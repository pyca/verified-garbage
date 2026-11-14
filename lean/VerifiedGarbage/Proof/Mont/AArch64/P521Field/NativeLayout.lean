module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The ordinary product's scratch region and full workspace offsets. -/

-- separate module: address bounds admit the higher affine-table prefix slots
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (off_off wordsVal_off Outside.of_off)

structure NativePre (s : State) (W o a b : Nat) : Prop where
  workspace : Scr s (s.gpr .x0) W
  scratch : 4016≤W
  output : o+72≤W
  inputA : a+72≤W
  inputB : b+72≤W
  scratchA : a+72≤3952 ∨ 4016≤a
  argO : s.gpr .x1=BitVec.ofNat 64 o
  argA : s.gpr .x2=BitVec.ofNat 64 a
  argB : s.gpr .x3=BitVec.ofNat 64 b

theorem workspace_ptr {s t : State} {base : Addr} {W d n : Nat} {r : Reg}
    (hs : Scr s base W) (hd : d+n≤W) (g : t.gpr r=off base d)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) : Ptr t r (off base d) n := by
  refine ⟨g,?_,by have h:=hs.enc; omega_arith⟩
  intro e he
  change InRegions (t.rd++t.wr) (off (off base d) e) 8
  rw [rd,wr,off_off]
  have h := hs.ld (d:=d+e) (by omega_arith)
  rw [hs.x0] at h
  exact h

theorem workspace_ptrW {s t : State} {base : Addr} {W d n : Nat} {r : Reg}
    (hs : Scr s base W) (hd : d+n≤W) (hn : 0<n) (g : t.gpr r=off base d)
    (wr : t.wr=s.wr) : PtrW t r (off base d) n := by
  refine ⟨g,?_,by have h:=hs.enc; omega_arith,?_⟩
  · intro e he
    change InRegions t.wr (off (off base d) e) 8
    rw [wr,off_off]
    have h := hs.st (d:=d+e) (by omega_arith)
    rw [hs.x0] at h
    exact h
  · have he := hs.enc
    have hf := hs.nowrap
    have hd64 : d<2^64 := by omega_arith
    have hdFit : base.toNat+d<2^64 := by omega_arith
    rw [VG.Offset.toNat_add_ofNat,Nat.mod_eq_of_lt hd64,Nat.mod_eq_of_lt hdFit]
    omega_arith

theorem stable_workspace_input {s : State} {W o a b : Nat} (hp : NativePre s W o a b) :
    StableInput s (off (s.gpr .x0) a) (off (s.gpr .x0) 3952) := by
  intro m hm d hd
  have h := Outside.of_off hm (by decide : 3952+64<2^64)
  have he := hp.workspace.enc
  have hb := hp.inputA
  have hs := hp.scratchA
  have e := h.word (d:=a+d) (by omega_arith) (by omega_arith)
  dsimp only [word]
  rw [off_off]
  exact e

end VG.Proof.Mont.AArch64.P521Field
