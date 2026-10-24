module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: drawing a witness

`dHead_ok`: the next `K = ⌈mb / 8⌉` octets of the tape at `used = u` into
array 4, `used := u + K`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN)
open VG.Proof.Mont (val32)

/-- Before a draw of a witness for the modulus `N` of `mb` bits, `u`
octets of the tape read. -/
structure DPre (p : PP) (mb N u : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb s
  prep : Prep s p.B p.n (wOf mb) N
  used : word s.mem p.B (8 * hUsed) = BitVec.ofNat 64 u
  room : u + (mb + 7) / 8 ≤ p.r.length
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The head of a draw: the octets' address in `r12`, their count in `r6`,
array 4's in `r10`, and `used` advanced. -/
theorem dHead_ok {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u s) :
    WP isa (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6,
        sth .r3 hUsed] ++ base .r10 4)) s fun t =>
      (t.gpr .r12 = p.rp + BitVec.ofNat 64 u ∧ t.gpr .r6 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
        t.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
        t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ∧
      Keep [.r3, .r6, .r12, .r10] s t := by
  rw [WP.block_append_iff]
  have hk := h.ph.kW
  have hu := h.used
  simp only [word, off, hK, hUsed, Nat.reduceMul] at hk hu
  refine WP.mono (WP.keep [.r3, .r6, .r12] (Q := fun u' => u'.gpr .r12 = p.rp + BitVec.ofNat 64 u ∧
      u'.gpr .r6 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
      u'.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ?_ (by decide))
    fun t₁ ⟨⟨a12, a6, am⟩, k₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK]
    prun [h.st.r31, h.st.ld (d := 136) (by decide), h.st.ld (d := 152) (by decide),
      h.st.ld (d := 216) (by decide), h.st.st (d := 152) (by decide), h.st.args.rand', hk, hu]
    simp only [BitVec.ofNat_add]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide)
    ((k₁.gpr .r10 (by decide)).trans h.ph.r10) ((k₁.gpr .r29 (by decide)).trans h.ph.r29) 4)
    fun t ⟨⟨a10, m⟩, k⟩ => ⟨⟨(k.gpr .r12 (by decide)).trans a12, (k.gpr .r6 (by decide)).trans a6, a10,
      m.trans am⟩, (k₁.trans k).mono (by decide)⟩

/-- The head and the load: the witness's octets in array 4. -/
theorem dLoad_ok {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u s) :
    WP isa (.seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6,
        sth .r3 hUsed] ++ base .r10 4)) loadN) s fun t =>
      (val32 t.mem p.B (slot (wOf mb) 4) (2 * wOf mb) = Spec.Rsa.os2ip ((p.r.drop u).take ((mb + 7) / 8)) ∧
        t.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
        Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)] s.mem t.mem ∧
        t.mem.readW (p.B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 (u + (mb + 7) / 8)) ∧
      Keep ([.r3, .r6, .r12, .r10] ++ [.r0, .r14, .r15, .r16, .r17]) s t := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hn := h.st.dims.n
  have hnw := h.st.scr.nowrap
  have hm1 := h.mb1
  have hm2 := h.mb2
  have hroom := h.room
  have h11 := h.ph.r11
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega
  have hKw : (mb + 7) / 8 ≤ 8 * w := by simp only [wOf] at hwd; omega
  have hZ : slot w 4 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega
  generalize hKd : (mb + 7) / 8 = K at *
  have hK1 : 1 ≤ K := by omega
  refine WP.seq (WP.mono (dHead_ok h) fun t ⟨⟨a12, a6, a10, am⟩, k₁⟩ => ?_)
  rw [hKd, hwd] at *
  have ho : Outside p.B 152 8 s.mem t.mem := by rw [am]; exact writeW_outside _ _ _ (by omega)
  have hbr : Spec.Rsa.bytesAt t.mem p.rp p.r.length = p.r := by
    rw [bytes_frm (Frm.of_outside (rs := [(152, 8)]) ho (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; simp only [PP.Z]; omega) h.st.bufs.sepR]
    exact h.st.bufs.bR
  have e : ∀ i, VG.Proof.Mont.off (p.rp + BitVec.ofNat 64 u) i = off p.rp (u + i) := fun i => off_off p.rp u i
  refine WP.mono (loadN_ok (N := p.rp + BitVec.ofNat 64 u) (h.st.scr.congr k₁.wr) a10
    (by rw [a12]; simp only [BitVec.add_zero]) a6 ((k₁.gpr .r11 (by decide)).trans h11) hK1 hKw
    (by omega) (by simp only [slot, hdrBytes]; omega) hZ
    (fun i hi => by
      rw [k₁.rd, k₁.wr, e]
      exact h.st.bufs.rdR _ (by omega))
    (fun i hi x hx => by
      rw [e]
      exact h.st.bufs.sepR _ (by omega) x hx)) fun t₂ ⟨v₂, o₂, k₂⟩ => ?_
  refine ⟨⟨?_, (k₂.gpr .r10 (by decide)).trans a10, ?_, ?_⟩, k₁.trans k₂⟩
  · rw [v₂, ← VG.Proof.Dsa.bytesAt_slice t.mem p.rp (total := p.r.length) (by omega), hbr]
  · exact (Frm.of_outside ho (List.mem_cons_self)).trans
      (Frm.of_outside o₂ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [show t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = word t₂.mem p.B 152 from rfl,
      Outside.word o₂ (by simp only [slot, hdrBytes]; omega) (by omega), am]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
