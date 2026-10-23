module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Rounds
public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Math
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The resident keys, the incomplete final XOR, and the preloaded next plaintext. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

abbrev live : List VReg := [.v0,.v1,.v31]
theorem live_regs : BlockRegs live := ⟨by decide,by decide⟩

structure Env (s₀ s : State) : Prop where
  keys : Keys (R s₀) (wK s₀) s
  folded : s.v .v7=s.v .v16 ^^^ s.v .v30
  iv : s.gpr .x11=Iv s₀
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr

theorem Env.transfer {s₀ s t : State} (h : Env s₀ s)
    (hv : ∀ r,r ∉ live → t.v r=s.v r) (h6 : t.gpr .x6=s.gpr .x6)
    (h7 : t.gpr .x7=s.gpr .x7) (h11 : t.gpr .x11=s.gpr .x11)
    (hm : t.mem=s.mem) (hrd : t.rd=s.rd) (hwr : t.wr=s.wr) : Env s₀ t := by
  refine ⟨h.keys.of_v live_regs hv h6 h7,?_,h11.trans h.iv,?_,hrd.trans h.rd,hwr.trans h.wr⟩
  · rw [hv _ (by decide),hv _ (by decide),hv _ (by decide),h.folded]
  · rw [hm]; exact h.frame

theorem Env.vframe {s₀ s t : State} (h : Env s₀ s) {rs : List VReg}
    (hf : VFrame rs s t) (hr : ∀ r ∈ rs,r ∈ live) : Env s₀ t :=
  h.transfer (fun r h => hf.v r (fun hm => h (hr r hm)))
    (congrFun hf.gpr _) (congrFun hf.gpr _) (congrFun hf.gpr _) hf.mem hf.rd hf.wr

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ N s₀
  env : Env s₀ s
  ptr : s.gpr .x2=blk s₀ k
  count : s.gpr .x3=BitVec.ofNat 64 (N s₀-k)
  chain : s.v .v31 ^^^ s.v .v30=chain s₀ k
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀)
  ready : k < N s₀ → s.v .v0=s₀.mem.readW (blk s₀ k) 128 ^^^ s.v .v7

theorem st_inj {p q : BitVec 128} (h : st p=st q) : p=q := by
  apply ext_vbyte
  intro i hi
  have hh := congrArg (fun x : Spec.Aes.State => x.getD i 0) h
  simpa only [getD_st _ hi] using hh

theorem value_pack {v : BitVec 128} {x : Spec.Aes.State} (h : st v=x) : v=pack x :=
  st_inj (h.trans (st_pack x).symm)

theorem original_read {s₀ s : State} {k j : Nat}
    (hi : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀))
    (hkj : k ≤ j) (hj : j < N s₀) : s.mem.readW (blk s₀ j) 128=s₀.mem.readW (blk s₀ j) 128 := by
  apply st_inj
  rw [st_readW,st_readW]
  exact ecbInv_orig hi hkj hj
end VG.Proof.AesCbc.AArch64.Encrypt
