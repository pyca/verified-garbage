module

import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
public import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage

/-! ### `MillerRabin.X86_64.FrameCT`, which only this module used -/

section

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

end

end

/-! ### `MillerRabin.X86_64.StackRegions`, which only this module used -/

section

/-! # The saved frames provide three disjoint writable regions -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem entered_kw {s : State} {B : Addr} {Z : Nat}
    (hw : s.wr = [⟨B, Z⟩]) (hz : 256 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩) :
    KW B (entered s).wr := by
  have h8 : Region.Disjoint ⟨s.gpr .rsp - 112#64, 8⟩ ⟨B, Z⟩ :=
    hd.sub_left (Offset.sub_below _ (a := 112) (n := 8) (b := 120) (m := 120) (by decide) (by decide))
  have h104 : Region.Disjoint ⟨s.gpr .rsp - 104#64, 104⟩ ⟨B, Z⟩ :=
    hd.sub_left (Offset.sub_below _ (a := 104) (n := 104) (b := 120) (m := 120) (by decide) (by decide))
  have hpair : Region.Disjoint ⟨s.gpr .rsp - 112#64, 8⟩ ⟨s.gpr .rsp - 104#64, 104⟩ := by
    rw [Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 104 ≤ 112)]
    exact Offset.base_disjoint _ (by decide) (by decide)
  refine ⟨⟨s.gpr .rsp - 112#64, 8⟩, ⟨s.gpr .rsp - 104#64, 104⟩, Z,
    ?_, by change 8 ≤ 104; decide, hz, ?_, ?_⟩
  · rw [entered_wr, hw]
    rfl
  · simp [entered_wr, hw, List.pairwise_cons, hpair, h8, h104]
  · simp only [entered_wr, hw, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith

end VG.Proof.MillerRabin.X86_64

end

end


/-! # The callable's public inputs supply the framed body's context -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def inputPub (s : State) : BodyPub :=
  ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8, Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi),
    [⟨s.gpr .rsp - 112#64, 8⟩, ⟨s.gpr .rsp - 104#64, 104⟩,
      ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩], s.gpr .rsp - 112#64⟩

/-- `FramePre`, and what the framed body's Montgomery calls need: the
workspace apart from the frames, and every buffer apart from the calls'
return address. -/
def FramePreC (p : BodyPub) (s : State) : Prop :=
  FramePre p s ∧ Region.Disjoint ⟨p.B, p.Z⟩ ⟨p.sp, 112⟩ ∧ Clear (hole p.sp) (entered s)

theorem stage_frame_call_ok {s : State} (h : roundPre s) :
    WP isa (.block stage) s (FramePreC (inputPub s)) := by
  obtain ⟨hdim, bm, hc, he, ho, h3, hx⟩ := initial_ctx h
  obtain ⟨hrd, hwr, hn, hs, hret, hstack, hL, hP⟩ := h
  let B := s.gpr .rdi
  let Z := (s.gpr .rsi).toNat * 8
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  obtain ⟨b, _, hb⟩ := witness_exists (coprime_pow2 ho (64 * w)) hx
  have hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb
  have hz : 256 ≤ Z := by
    have := hdr_lt_slot w 8 (show 31 < 32 by decide)
    have hz0 : slot w 8 ≤ Z := hdim.z
    omega_arith
  refine WP.mono (stage_ok hc.good hdim.z) ?_
  rintro t ⟨hm, hv, hk⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hst : 120 ≤ (t.gpr .rsp).toNat := hsp ▸ hs
  have hdt : Region.Disjoint ⟨t.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩ := by
    rw [hsp]
    exact hstack
  have hd : Region.Disjoint ⟨t.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩ :=
    hdt.sub_left (Offset.sub_below _ (a := 112) (n := 112) (b := 120) (m := 120) (by decide) (by decide))
  obtain ⟨hct, het⟩ := staged_context hc he hm hk
  have hce := entered_ctx hct hdim hst hd
  have hee := entered_exp het hdim hst hn hd
  have hxe : wv (entered t).mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [entered_wv hst hn hd (by
      have := slot_le (w := w) (show aXm < 8 by decide)
      have hz0 : slot w 8 ≤ Z := hdim.z
      omega_arith), hm]
    exact hX
  have hw : (entered t).wr = (inputPub s).wr := by
    rw [entered_wr, hk.2.2, hwr, hsp]
    rfl
  have hkw := entered_kw (hk.2.2.trans hwr) hz hn hdt
  have hcl := entered_clear (hk.2.1.trans hrd) (hk.2.2.trans hwr) hdt
  rw [entered_rsp, hsp] at hcl
  refine ⟨⟨⟨?_, ?_, hdim, _, c, bm, b, hce, hee, ho, h3, hxe⟩, hw⟩, ?_, hcl⟩
  · rw [entered_rsp, hsp]
    rfl
  · rw [hw] at hkw
    exact hkw
  · show Region.Disjoint ⟨B, Z⟩ ⟨s.gpr .rsp - 112#64, 112⟩
    rw [← hsp]
    exact hd.symm

theorem stage_frame_ok {s : State} (h : roundPre s) :
    WP isa (.block stage) s (FramePre (inputPub s)) :=
  WP.mono (stage_frame_call_ok h) fun _ h => h.1

end VG.Proof.MillerRabin.X86_64
