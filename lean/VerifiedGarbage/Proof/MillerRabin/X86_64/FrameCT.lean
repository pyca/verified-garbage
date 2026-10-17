module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack

/-! # Constant time through both saved frames -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64 VG.Proof.Bignum.X86_64

def FramePre (p : BodyPub) (s : State) : Prop :=
  BodyPre p (entered s) ∧ (entered s).wr = p.wr

private theorem frame_sp {s t : State} (h : Two FramePre s t) : s.gpr .rsp = t.gpr .rsp := by
  obtain ⟨p, hs, ht⟩ := h
  have h1 := hs.1.1
  have h2 := ht.1.1
  rw [entered_rsp] at h1 h2
  bv_omega

theorem frames_ct (M : Mont) : RelCT isa (Two FramePre)
    (.frame (.push saved)
      (.frame (.push [.rbp]) (VG.Impl.MillerRabin.X86_64.body M.mm) (.pop .rbp 1))
      (.pop .r11 13)) fun _ _ => True := by
  apply RelCT.frame (fun _ _ h => frame_sp h)
  apply RelCT.frame (fun a b h => by
    obtain ⟨s, t, hp, rfl, rfl⟩ := h
    rw [pushed_rsp, pushed_rsp, frame_sp hp])
  refine (body_ct M).mono ?_ (fun _ _ h => h)
  rintro a b ⟨u, v, ⟨s, t, ⟨p, hs, ht⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨p, hs, ht⟩

end VG.Proof.MillerRabin.X86_64
