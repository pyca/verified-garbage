module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Entry

/-! The ciphertext, tag and saved caller state shared by the direct gather paths. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gctr fullTag)

abbrev changed (s : State) : List Region := [⟨W s, 2560⟩, dR s, below (SP s) 56]

structure BodyDone (_M : CtxMode) (s t : State) : Prop where
  env : Env (K s) (W s + 16#64) (W s) (SP s) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : SavedAt t.mem (W s) s
  frame : Frame (changed s) s.mem t.mem
  cipher : bytesAt t.mem (Dst s) (L s) = gctr (ciph s) (icb s) (pt s (Cnt s))
  tag : bytesAt t.mem (W s) 16 =
    fullTag (ciph s) (hk s) (iv s) (ad s) (bytesAt t.mem (Dst s) (L s))

end VG.Proof.AesGcm.X86_64.DirectGather
