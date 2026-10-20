module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.StageFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.MillerRabin.X86_64.BoundaryCT

/-!
# Constant time of the round with Montgomery calls

The round's body `code` calls the Montgomery multiplication where
`body M.mm` runs it inline (`code.inline = body M.mm`). Within the frames,
the body's run exists (`body_ok`) and keeps every buffer off the calls'
return address (`FramePreC`), so `RelCT.of_inline` gives `code` the
leakage of `body M.mm` (`body_ct`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64 VG.Proof.Bignum.X86_64

private theorem framec_sp {s t : State} (h : Two FramePreC s t) : s.gpr .rsp = t.gpr .rsp := by
  obtain ⟨p, hs, ht⟩ := h
  have h1 := hs.1.1.1
  have h2 := ht.1.1.1
  rw [entered_rsp] at h1 h2
  bv_omega

private theorem framec_run (M : Mont) {code : Prog isa}
    (hcode : code.inline = VG.Impl.MillerRabin.X86_64.body M.mm) {p : BodyPub} {s : State} (h : FramePreC p s) :
    ∃ t s', Exec isa code.inline (entered s) t s' := by
  obtain ⟨⟨⟨hsp, _, hdim, mi, c, bm, b, hc, he, ho, h3, hx⟩, _⟩, hd, _⟩ := h
  rw [hcode]
  obtain ⟨t, s', he', _⟩ := body_ok M hc hdim he ho h3 hx hsp hd fun d hlo hhi => by
    rw [← hsp]
    exact entered_load s hlo hhi
  exact ⟨t, s', he'⟩

private theorem framec_clear {p : BodyPub} {s : State} (h : FramePreC p s) :
    Clear (hole ((entered s).gpr .rsp)) (entered s) := by
  rw [h.1.1.1]
  exact h.2.2

theorem frames_call_ct (M : Mont) {code : Prog isa} (hi : code.InlineOk = true)
    (hcode : code.inline = VG.Impl.MillerRabin.X86_64.body M.mm) :
    RelCT isa (Two FramePreC)
      (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13)) fun _ _ => True := by
  apply RelCT.frame (fun _ _ h => framec_sp h)
  apply RelCT.frame (fun a b h => by
    obtain ⟨s, t, hp, rfl, rfl⟩ := h
    rw [pushed_rsp, pushed_rsp, framec_sp hp])
  refine RelCT.of_inline hi ?_ ?_ ?_ ?_
  · rintro a b ⟨u, v, ⟨s, t, ⟨p, hs, ht⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨framec_run M hcode hs, framec_run M hcode ht⟩
  · rintro a b ⟨u, v, ⟨s, t, ⟨p, hs, ht⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨framec_clear hs, framec_clear ht⟩
  · rintro a b ⟨u, v, ⟨s, t, ⟨p, hs, ht⟩, rfl, rfl⟩, rfl, rfl⟩
    exact hs.1.1.1.trans ht.1.1.1.symm
  · rw [hcode]
    refine (body_ct M).mono ?_ (fun _ _ h => h)
    rintro a b ⟨u, v, ⟨s, t, ⟨p, hs, ht⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨p, hs.1, ht.1⟩

private def RoundState (p : BodyPub) (s : State) : Prop :=
  roundPre s ∧ inputPub s = p

private theorem inputPub_eq {s t : State} (hp : roundPub s t) : inputPub s = inputPub t := by
  obtain ⟨hsp, hdi, hsi, hw⟩ := hp
  unfold inputPub
  congr 1
  · rw [hsi]
  · rw [hsp, hdi, hsi]
  · rw [hsp]

/-- The round, with the body `code`, is constant time. -/
theorem round_call_ct (M : Mont) {code : Prog isa} (hi : code.InlineOk = true)
    (hcode : code.inline = VG.Impl.MillerRabin.X86_64.body M.mm) :
    ConstantTime isa roundPre roundPub
      (.seq (.block stage) (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13))) := by
  have hrel : RelCT isa (Two RoundState)
      (.seq (.block stage) (.frame (.push saved) (.frame (.push [.rbp]) code (.pop .rbp 1)) (.pop .r11 13)))
      fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := FramePreC) ?_ ?_) (frames_call_ct M hi hcode)
    · refine stage_ct.mono ?_ (fun _ _ h => h)
      rintro s t ⟨p, hs, ht⟩
      refine ⟨p.B, ?_, ?_⟩
      · exact congrArg BodyPub.B hs.2
      · exact congrArg BodyPub.B ht.2
    · intro p s h
      rw [← h.2]
      exact stage_frame_call_ok h.1
  apply RelCT.constantTime
  refine hrel.mono ?_ (fun _ _ h => h)
  rintro s t ⟨hs, ht, hp⟩
  exact ⟨inputPub s, ⟨hs, rfl⟩, ht, (inputPub_eq hp).symm⟩

end VG.Proof.MillerRabin.X86_64
