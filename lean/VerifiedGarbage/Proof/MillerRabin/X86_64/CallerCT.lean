module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Constant time of the complete shared-round caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller

private theorem ready_base {L : Public} {s : State} (h : Ready L s) :
    s.gpr .rdi = L.ws.B := by
  obtain ⟨⟨mi, c, bm, b, hc, _⟩, _⟩ := h
  exact hc.good.rdi

private theorem ready_sp {L : Public} {s : State} (h : Ready L s) :
    s.gpr .rsp = L.sp := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, _⟩, _⟩ := h
  exact hsp

private theorem ready_width {L : Public} {s : State} (h : Ready L s) :
    Proof.Rsa.Mont.wOf (narrowed s L.ws.B L.ws.w).mem L.ws.B = L.ws.w := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, _⟩, _⟩ := h
  obtain ⟨hce, _⟩ := entry_context hc he hd hr.disjoint
  change Proof.Rsa.Mont.wOf s.callEntry.mem L.ws.B = L.ws.w
  exact ctx_width hce hd.w128

private theorem ready_pub {L : Public} {s t : State} (hs : Ready L s) (ht : Ready L t) :
    roundPub (narrowed s L.ws.B L.ws.w) (narrowed t L.ws.B L.ws.w) := by
  have hbs : (narrowed s L.ws.B L.ws.w).gpr .rdi = L.ws.B :=
    (s.callEntry_gpr (by decide)).trans (ready_base hs)
  have hbt : (narrowed t L.ws.B L.ws.w).gpr .rdi = L.ws.B :=
    (t.callEntry_gpr (by decide)).trans (ready_base ht)
  have hns : (narrowed s L.ws.B L.ws.w).gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w) :=
    (s.callEntry_gpr (by decide)).trans hs.2.2
  have hnt : (narrowed t L.ws.B L.ws.w).gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w) :=
    (t.callEntry_gpr (by decide)).trans ht.2.2
  refine ⟨?_, hbs.trans hbt.symm, hns.trans hnt.symm, ?_⟩
  · change s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
    rw [State.callEntry_rsp, State.callEntry_rsp, ready_sp hs, ready_sp ht]
  · rw [hbs, hbt]
    exact (ready_width hs).trans (ready_width ht).symm

private theorem prepared_call_ct (v : RoundImpl) :
    RelCT isa (Two Ready) (.call v.name v.code) fun _ _ => True := by
  apply RelCT.callEx (k := roundContract) v.correct v.ct
  rintro s t ⟨L, hs, ht⟩
  have hcs := ready_covers hs
  have hct := ready_covers ht
  exact ⟨[], [⟨L.ws.B, 8 * callWords L.ws.w⟩], [], [⟨L.ws.B, 8 * callWords L.ws.w⟩],
    ready_pre hs, ready_pre ht, ready_pub hs ht, hcs.1, hcs.2, hct.1, hct.2,
    (ready_sp hs).trans (ready_sp ht).symm⟩

theorem call_ct (v : RoundImpl) :
    RelCT isa (Two Before) (call v.name v.code) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  refine RelCT.seq (two_post (Ψ := Ready) ?_ (fun _ _ h => save_ready h)) ?_
  · exact two_map Public.ws (fun _ _ h => before_save h) save_ct
  · exact RelCT.seq (two_post (prepared_call_ct v) (fun _ _ h => call_restore_pre v h))
      (two_map Public.ws (fun _ _ h => h) restore_ct)

end VG.Proof.MillerRabin.X86_64.Caller
