module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post

/-! Boundary between encrypting the gathered pieces and authenticating the remaining ciphertext. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gctr blockAt j0 zeros padLen)
open VG.Proof.Gcm (Absorbed)

structure TextDone (_M : CtxMode) (s t : State) (pre : Nat) : Prop where
  env : Env (K s) (W s+16#64) (W s) (SP s) t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  saved : SavedAt t.mem (W s) s
  frame : Frame (changed s) s.mem t.mem
  cipher : bytesAt t.mem (Dst s) (L s)=gctr (ciph s) (icb s) (pt s (Cnt s))
  «prefix» : pre≤L s
  aligned : pre%16=0
  data : t.mem.readW (W s+200#64) 64=Dst s+BitVec.ofNat 64 pre
  len : t.mem.readW (W s+208#64) 64=BitVec.ofNat 64 (L s-pre)
  total : t.mem.readW (W s+192#64) 64=BitVec.ofNat 64 (L s)
  aad : t.mem.readW (W s+184#64) 64=AL s
  rounds : RoundsAt t.mem (W s) (R s)
  key : ciphOf t.mem (K s) (R s)=ciph s
  hkey : blockAt t.mem (K s+240#64)=hk s
  j0 : blockAt t.mem (W s+16#64)=Spec.Gcm.j0 (hk s) (iv s)
  auth : Absorbed t.mem (W s+16#64+16#64) (W s+16#64+32#64) (hk s)
    (ad s ++ zeros (padLen (ad s).length) ++ bytesAt t.mem (Dst s) pre)

end VG.Proof.AesGcm.X86_64.DirectGather
