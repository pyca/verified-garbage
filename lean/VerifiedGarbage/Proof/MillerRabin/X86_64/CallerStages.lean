module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerBoundaryCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.Framework.Omega

/-! # Contexts before and after the actual shared round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller

structure Public where
  ws : Ws
  sp : Addr

def Before (L : Public) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat),
    MrCtx s L.ws.B L.ws.Z L.ws.w mi c bm ∧ ECtx s.mem L.ws.B L.ws.w c ∧
    MrDims L.ws.B L.ws.Z L.ws.w ∧ slot L.ws.w 28 ≤ L.ws.Z ∧
    Room s L.ws.B L.ws.Z ∧ s.gpr .rsp = L.sp ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    wv s.mem L.ws.B (slot L.ws.w aXm) L.ws.w = b % c * 2 ^ (64 * L.ws.w) % c

def Ready (L : Public) (s : State) : Prop :=
  Before L s ∧ s.gpr .rbx = L.ws.B ∧ s.gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w)

theorem before_save {L : Public} {s : State} (h : Before L s) : SavePre L.ws s := by
  obtain ⟨mi, c, bm, b, hc, _, _, hz, _⟩ := h
  exact ⟨mi, hc.good, hz⟩

theorem save_ready {L : Public} {s : State} (h : Before L s) :
    WP isa (.block save) s (Ready L) := by
  obtain ⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good hz) ?_
  rintro t ⟨hm, hb, hn, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hd hm hk
  have hts : t.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hrt : Room t L.ws.B L.ws.Z := ⟨by rw [hts]; exact hr.size,
    by rw [hts]; exact hr.disjoint⟩
  refine ⟨⟨mi, c, bm, b, hct, het, hd, hz, hrt, hts.trans hsp, ho, h3, ?_⟩, hb, hn⟩
  have hp : pad L.ws.w + 8 ≤ 2 ^ 64 := by
    have hs := hc.good.scr.nowrap
    simp only [pad, slot, hdrBytes, aR1] at hz ⊢
    omega_arith
  rw [hm, (saved_outside s L.ws.B L.ws.w hp).wv (Or.inl (by
    simp only [pad, slot, hdrBytes, aR1, aXm]; omega_arith)) (by
      have hs := hc.good.scr.nowrap
      simp only [slot, hdrBytes, aXm] at hz ⊢
      omega_arith)]
  exact hx

theorem ready_pre {L : Public} {s : State} (h : Ready L s) :
    roundPre (narrowed s L.ws.B L.ws.w) := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩, hb, hn⟩ := h
  apply narrow_pre hc he hd hz hr hn ho h3
  rw [hx]
  exact Nat.mod_lt _ (by omega_arith)

theorem ready_covers {L : Public} {s : State} (h : Ready L s) :
    Covers ([] ++ [⟨L.ws.B, 8 * callWords L.ws.w⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨L.ws.B, 8 * callWords L.ws.w⟩] s.wr := by
  obtain ⟨⟨mi, c, bm, b, hc, _, _, hz, _⟩, _⟩ := h
  exact narrow_covers hc.good.scr hz

theorem call_restore_pre (v : RoundImpl) {L : Public} {s : State} (h : Ready L s) :
    WP isa (.call v.name v.code) s (RestorePre L.ws) := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩, hb, hn⟩ := h
  refine WP.mono (round_call_ok v hc he hd hz hr hn ho h3 hx) ?_
  rintro t ⟨hcs, hrd, hwr, hf, hresult, hkeep, hmx⟩
  refine ⟨hc.good.scr.congr hwr, hz, (hcs .rbx (by decide)).trans hb, ?_⟩
  exact (kept_header hkeep (by unfold callWords; omega_arith) (by decide) (by decide)).trans hc.good.hdr.hw

end VG.Proof.MillerRabin.X86_64.Caller
