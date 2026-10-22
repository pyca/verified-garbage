module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Choose the 128-byte selector for widths that are a multiple of 16 limbs,
and the 64-byte one for the other multiples of 8, by the public width. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx SelP)

def wideGuard : List Instr := [ldh .x12 sW, movi .x4 15, .logic .and .x .x4 .x12 .x4]

theorem vector_eq : VG.Impl.Rsa.AArch64.WindowSelectVector.vector 32 =
    .seq (.block wideGuard) (.ite (.zero .x .x4)
      (VG.Impl.Rsa.AArch64.WindowSelectVector.wide 32)
      (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32)) := rfl

theorem mask15_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.setWidth 64 (BitVec.ofNat 16 15) =
      BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 (BitVec.ofNat 16 15)).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n % 16 < 2 ^ 64 by omega)]

theorem wideGuard_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : w < 2 ^ 30) :
    WP isa (.block wideGuard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x4 = BitVec.ofNat 64 (w % 16)) ∧ Keep [.x12,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [wideGuard, hc.good.x0, hdr_enc (show sW < 32 by decide), hc.ld (i := sW) (by decide),
    hc.good.hdr.hw, mask15_ofNat (show w < 2 ^ 64 by omega)]

theorem vector_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 8 = 0)
    (hv : v < 32) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.vector 32) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [vector_eq]
  refine WP.seq (WP.mono (wideGuard_ok hc hw') fun u ⟨⟨hm,h4⟩,ku⟩ => ?_)
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have tab : word u.mem P (8 * Crt.sTab) = off P (slot w 8) := by rw [hm]; exact ht
  have nib : word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v := by rw [hm]; exact hN
  by_cases h16 : w % 16 = 0
  · refine WP.ite true (by rw [eval_zero,h4,h16]; rfl) (fun _ => ?_) (by simp)
    exact WP.mono (wide_ok ctx (by omega) hw' h16 hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
      ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
  · refine WP.ite false (by rw [eval_zero,h4,eq_zero_iff,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show w % 16 < 2 ^ 64 by omega),decide_eq_false h16]) (by simp) (fun _ => ?_)
    exact WP.mono (blocked_ok ctx hw hw' hd hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
      ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩

structure WideGuardCtx (p : XPub) (s : State) : Prop where
  pre : BlockPre p s
  rem : s.gpr .x4 = BitVec.ofNat 64 (p.wx % 16)

theorem wideGuard_ready {p : XPub} {s : State} (h : BlockPre p s) :
    WP isa (.block wideGuard) s (WideGuardCtx p) := by
  obtain ⟨⟨mi,X,Xc,v,hc,hw,hw',hv,ht,hN⟩,h8⟩ := h
  refine WP.mono (wideGuard_ok hc hw') fun u ⟨⟨hm,h4⟩,ku⟩ => ?_
  exact ⟨⟨⟨mi,X,Xc,v,hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr
    (ku.gpr .x0 (by decide)),hw,hw',hv,hm ▸ ht,hm ▸ hN⟩,h8⟩,h4⟩

theorem wideGuard_mod {p : XPub} {s : State} (h : WideGuardCtx p s)
    (ht : isa.eval (.zero .x .x4) s = some true) : p.wx % 16 = 0 := by
  rw [eval_zero,h.rem,eq_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx % 16 < 2 ^ 64 by omega)] at ht
  exact of_decide_eq_true (Option.some.inj ht)

theorem vector_ct : RelCT isa (Two BlockPre)
    (VG.Impl.Rsa.AArch64.WindowSelectVector.vector 32) (fun _ _ => True) := by
  rw [vector_eq]
  refine RelCT.seq (two_piece (Ψ := WideGuardCtx) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0))
    (by taint_decide) (fun _ _ h => wideGuard_ready h)) ?_
  refine two_ite (Φ := WideGuardCtx) ?_ ?_ ?_
  · intro p s t hs ht
    rw [eval_zero,eval_zero,hs.rem,ht.rem]
  · exact two_map id (fun p _ h => ⟨h.1.pre.1,show 16 ≤ p.wx by
      have := wideGuard_mod h.1 h.2; have := h.1.pre.2; omega,
      wideGuard_mod h.1 h.2⟩) wide_ct
  · exact two_map id (fun _ _ h => h.1.pre) blocked_ct

end VG.Proof.Bignum.AArch64.WindowVector
