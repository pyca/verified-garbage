module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunCT
import VerifiedGarbage.Proof.Bignum.Math

/-! Constant time for wider-table prime exponentiation under the existing key bounds. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt (ldw)

def runPub (a : BPub) : RunPub := ⟨a.x,a.ptr,a.len⟩

theorem expHead_post (M : Mont) {sp sl : Nat} {a : BPub} {s : State}
    (h : EPreWide sp sl a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) s (RunInv (runPub a) 0 0) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨mi,X,x,y,bs,hctx,hw2,hwx,hw30,hn,hinv,hodd,hxl,_,hyl,_,hsp,hsl,hep,hel,hL,_,hL2,he⟩ := h
  have hT : Scr s (off a.x.B a.x.o) (slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx) :=
    hctx.scr.sub (by omega) (by unfold slot hdrBytes; omega)
  have hout : ∀ i < bs.length, slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx ≤
      ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) := by
    intro i hi
    have := he.out i hi
    have hn := hctx.scr.nowrap
    have hp := hT.nowrap
    have hslot : 0 < slot a.x.wx 8 := by unfold slot hdrBytes; omega
    rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega) with ⟨_,h2⟩ | ⟨h1,_⟩
    · omega
    · omega
  refine WP.mono (expHead_ok M (Q := False) (x := 0) hctx hT hw2 hwx hw30 hn hinv hodd
    hxl False.elim hyl False.elim hsp hsl hep hel) fun t ht => ?_
  exact ⟨s,mi,X,_,bs,ht,hw2,by dsimp [runPub]; omega,VG.Proof.Bignum.coprime_pow2 hodd _,hL,by dsimp [runPub]; omega,
    he.rd,he.val,hout⟩

theorem expLoop_ct (W : Window) (M : Mont) (S : Selector) {sp sl : Nat}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl))
      (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expLoop
  exact RelCT.seq (two_post (Ψ := fun a => RunInv (runPub a) 0 0) (expHead_ct M hT)
    (fun _ _ h => expHead_post M h)) (two_map runPub (fun _ _ h => h) (expRun_ct W M S))

end VG.Proof.Bignum.AArch64.WindowFive
