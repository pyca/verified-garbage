module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit

/-! A tail bit's branch depends only on the public pending-bit count. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (takeBit)

def TailPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc v V, TableCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0 ∧
    wv s.mem (off p.1.B p.1.o) (slot p.1.wx aY) p.1.wx < X ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ p.2 < 5 ∧ v < 2 ^ p.2 ∧ V < 256 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 v ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sBit) = BitVec.ofNat 64 p.2 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧
    Nat.Coprime (2 ^ (64 * p.1.wx)) X

structure TailReady (p : XPub × Nat) (s : State) : Prop where
  raw : RawWindowPre p.1 s
  flag : s.gpr .x3 = BitVec.ofNat 64 (p.2 + 1) - BitVec.ofNat 64 5

theorem prepare_ready {i : Nat} (hi : i < 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (.block (VG.Impl.Rsa.AArch64.WindowFive.prepareBit i)) s (TailReady p) := by
  obtain ⟨mi,X,Xc,v,V,hc,ht,hy,hw,hw',hb,hv,hV,hn,bc,byc,_⟩ := h
  refine WP.mono (prepareBit_state hc hi (pending_lt16 hb hv) hV hn bc byc)
    fun u ⟨cu,yu,nu,_,fu,_,_,flag⟩ => ?_
  exact ⟨⟨mi,X,Xc,2 * v + V / 2 ^ (7 - i) % 2,cu,
    ht.of_win fu hc.scrT.nowrap,yu.symm ▸ hy,hw,hw',by have := pending_lt16 hb hv; omega,nu⟩,flag⟩

theorem takeBit_ct (W : Window) {i : Nat} (hi : i < 8) :
    RelCT isa (Two TailPre) (takeBit W.code i) (fun _ _ => True) := by
  unfold takeBit
  refine RelCT.seq (two_post (Ψ := TailReady)
    (two_map (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨_,_,_,_,_,hc,_⟩ => hc.good.x0) (prepareBit_ct i))
    (fun _ _ h => prepare_ready hi h)) ?_
  refine two_ite (Φ := TailReady) ?_ ?_ ?_
  · intro p s t hs ht
    change some (s.gpr .x3 == 0) = some (t.gpr .x3 == 0)
    rw [hs.flag,ht.flag]
  · exact two_map Prod.fst (fun _ _ h => h.1.raw) W.ct
  · apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl

end VG.Proof.Bignum.AArch64.WindowFive
