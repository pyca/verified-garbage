module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv


/-! The outer loops preserve source bytes and the exact consumed exponent prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

structure PrefixInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc : Nat)
    (Q : Prop) (x : Nat) (ep : Addr) (bs : List Byte) (i b : Nat) (t : State) : Prop where
  ctx : TableCtx t P w mi X Xc
  tab : CrtWindowFive.CTab t.mem P w X Q x
  pending : Pending t P w X Q x b (pre bs i)
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  exp : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 bs.length
  frm : Frm P (CrtWindowFive.crtExpRanges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem PrefixInv.source {s t : State} {P ep : Addr} {w i b : Nat} {mi : BitVec 64}
    {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (h : PrefixInv s P w mi X Xc Q x ep bs i b t)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    {j : Nat} (hj : j < bs.length) : t.mem (ep + BitVec.ofNat 64 j) = bs[j] := by
  rw [h.frm _ fun r hr => Or.inr (by
    have := (CrtWindowFive.crtExpRanges_ok w r hr).2
    have := hout j hj
    omega)]
  exact hbytes j hj

theorem win_header {m m' : Mem} {P : Addr} {w k : Nat}
    (hf : Frm P (crtWinRanges w) m m')
    (hk : k < 32) (h1 : k ≠ Crt.sV) (h2 : k ≠ Crt.sBit) (h3 : k ≠ Crt.sNib)
    (h4 : k ≠ Crt.sEnt) (h5 : k ≠ Crt.sJ) : word m' P (8*k) = word m P (8*k) :=
  hf.word_eq (crtWinRanges_hdr w hk h1 h2 h3 h4 h5) (by
    omega)

theorem PrefixInv.keepMem {s t u : State} {P ep : Addr} {w i b : Nat} {mi : BitVec 64}
    {X Xc x : Nat} {Q : Prop} {bs : List Byte} {rs : List Reg}
    (h : PrefixInv s P w mi X Xc Q x ep bs i b t) (hm : u.mem = t.mem)
    (hk : Keep rs t u) (h0 : .x0 ∉ rs) (hrs : ∀ r ∈ rs, r ∈ mmRegs) :
    PrefixInv s P w mi X Xc Q x ep bs i b u := by
  have hf : Frm P (crtWinRanges w) t.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  exact ⟨h.ctx.of_win hf hk.wr (hk.gpr .x0 h0),hm.symm ▸ h.tab,
    by simpa only [Pending,hm] using h.pending,hm.symm ▸ h.idx,hm.symm ▸ h.exp,hm.symm ▸ h.len,
    hm.symm ▸ h.frm,(h.keep.trans (hk.mono hrs)).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowFive
