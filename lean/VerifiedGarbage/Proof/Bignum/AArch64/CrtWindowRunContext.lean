module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReadCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
import VerifiedGarbage.Proof.Bignum.CrtWindowFive

/-! Only the workspace layout, exponent address, length, and progress are public. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

structure RunPub where
  ws : XPub
  ep : Addr
  len : Nat

def RunInv (p : RunPub) (i b : Nat) (t : State) : Prop :=
  ∃ (s : State) (mi : BitVec 64) (X Xc : Nat) (bs : List Byte), PrefixInv s (off p.ws.B p.ws.o) p.ws.wx mi X Xc False 0 p.ep bs i b t ∧
    2 ≤ p.ws.wx ∧ p.ws.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.ws.wx)) X ∧
    bs.length = p.len ∧ p.len < 2 ^ 64 ∧
    (∀ j < bs.length, InRegions (s.rd ++ s.wr) (p.ep + BitVec.ofNat 64 j) 1) ∧
    (∀ j (hj : j < bs.length), s.mem (p.ep + BitVec.ofNat 64 j) = bs[j]) ∧
    (∀ j < bs.length, slot p.ws.wx 8 + CrtWindowFive.tabBytes32 p.ws.wx ≤
      ofs (off p.ws.B p.ws.o) (p.ep + BitVec.ofNat 64 j))

theorem RunInv.read {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    ReadPre (p.ws,p.ep,i) t := by
  obtain ⟨s,mi,X,Xc,bs,hI,_⟩ := h
  exact ⟨mi,X,Xc,hI.ctx,hI.exp,hI.idx⟩

theorem RunInv.x0 {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    t.gpr .x0 = off p.ws.B p.ws.o := by
  obtain ⟨s,mi,X,Xc,bs,hI,_⟩ := h
  exact hI.ctx.good.x0

theorem RunInv.finish {p : RunPub} {i b : Nat} {t : State} (h : RunInv p i b t) :
    FinishPre (p.ws,b) t := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,_⟩ := h
  obtain ⟨E,v,hb,hv,_,hy,_,hn,bc⟩ := hI.pending
  exact ⟨⟨mi,X,Xc,v,hI.ctx,hI.tab,hy,hw,hw',hR,CrtWindowFive.pending_index hv hb,hn⟩,hb,bc⟩

end VG.Proof.Bignum.AArch64.WindowFive
