module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStoresCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateLoadState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmeticCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
/-! # Candidate arithmetic accepts the persistent frame's actual words -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/CandidateBuildCT.lean`, which only this module imported.
section

/-! # The complete byte-to-byte p-candidate builder has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64

structure CandidateBuildPublic where
  input : CandidatePublic
  p : Addr
  exponent : Addr

def CandidateBuildPublic.outputs (p : CandidateBuildPublic) : CandidateOutputs :=
  ⟨p.input.B, p.input.Z, p.input.w, p.p, p.exponent⟩

def CandidateBuildState (p : CandidateBuildPublic) (s : State) : Prop :=
  CandidateInput p.input s ∧ CandidateStoreState p.outputs s

theorem candidateArithmetic_storeState {p : CandidateBuildPublic} {s : State} (h : CandidateBuildState p s) :
    WP isa Impl.Dsa.X86_64.Generation.candidateArithmetic s (CandidateStoreState p.outputs) := by
  have hw : Ws s p.input.B p.input.Z p.input.w := h.1.x.ws
  refine WP.mono (candidateArithmetic_ok hw h.1.x.pointer h.1.x.length h.1.q.pointer h.1.q.length
    h.1.x.source h.1.q.source h.1.x.positive h.1.x.fits h.1.q.positive h.1.q.fits
    h.1.qPositive h.1.qFits) fun t ⟨ht, _, _, f, hk⟩ => ?_
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.input.B d = word s.mem p.input.B d := by
    apply f.word_eq
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        left <;> simp only [slot, hdrBytes] <;> omega
    · have := hw.h256; have := hw.scr.nowrap; omega
  exact ⟨⟨ht, (header 160 (by decide)).trans h.2.1.pointer,
    (header 136 (by decide)).trans h.2.1.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.1.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.1.write i hi), h.2.1.outside⟩,
    ⟨ht, (header 168 (by decide)).trans h.2.2.pointer,
    (header 136 (by decide)).trans h.2.2.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.2.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.2.write i hi), h.2.2.outside⟩⟩

theorem candidateBuild_ct : RelCT isa (Two CandidateBuildState)
    Impl.Dsa.X86_64.Generation.candidateBuild (fun _ _ => True) :=
  RelCT.seq (two_post (two_map CandidateBuildPublic.input (fun _ _ h => h.1) candidateArithmetic_ct)
    (fun _ _ h => candidateArithmetic_storeState h))
    (two_map CandidateBuildPublic.outputs (fun _ _ h => h) candidateStores_ct)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  Z : Nat
  w : Nat
  xb : List Byte
  qb : List Byte
  xLength : xb.length = 8 * w
  qLength : qb.length ≤ 8 * w
  qNonempty : 1 ≤ qb.length
  qPositive : 0 < Spec.Rsa.os2ip qb
  qFits : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w)
  separate : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8
  pOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena p) i)
  eOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena exponent) i)

def CandidateFramePublic.build (c : CandidateFramePublic) : CandidateBuildPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena shaped, off c.arena q, c.xb, c.qb⟩,
    off c.arena p, off c.arena exponent⟩

def CandidateFramePublic.pointers (c : CandidateFramePublic) : ArgumentPointers := ⟨c.B, c.F⟩

structure CandidateFrameInputs (c : CandidateFramePublic) (s : State) : Prop where
  stack : s.gpr .rsp = c.F
  read : ∀ k < 37, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
  arena : word s.mem c.F 40 = c.arena
  x : Src s c.B c.Z (off c.arena shaped) c.xb
  q : Src s c.B c.Z (off c.arena q) c.qb
  pWrite : ∀ i < 8 * c.w, InRegions s.wr (off (off c.arena p) i) 1
  eWrite : ∀ i < 8 * c.w, InRegions s.wr (off (off c.arena exponent) i) 1

def CandidateFrameBefore (pLen qLen : Nat) (c : CandidateFramePublic) (s : State) : Prop :=
  CandidateFrameInputs c s ∧ Ws s c.B c.Z c.w ∧ c.xb.length = pLen ∧ c.qb.length = qLen

theorem candidateFrame_ready {pLen qLen : Nat} {c : CandidateFramePublic} {s : State}
    (h : CandidateFrameBefore pLen qLen c s) :
    WP isa (.block (headerArguments (candidateArguments pLen qLen))) s (CandidateBuildState c.build) := by
  have hp : pLen < 2 ^ 31 := by omega_using [h.2.1.w2, c.xLength, h.2.2.1]
  have hq : qLen < 2 ^ 31 := by omega_using [hp, c.qLength, c.xLength, h.2.2.1, h.2.2.2]
  have hw := candidateArguments_ok h.2.1 hp hq h.1.stack h.1.read
    (W := fun k => word s.mem c.F (8 * k)) (fun _ _ => rfl) c.separate
  refine WP.mono hw fun t ⟨ht, hxp, hxl, hqp, hql, hpp, hep, hm, hf, hk⟩ => ?_
  have frame : Frm c.B [(128, 128)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ c.Z := by
    simp only [List.mem_singleton, forall_eq]; exact h.2.1.h256
  have sx := h.1.x.congrK (InScr.of_frm frame bound) hk
  have sq := h.1.q.congrK (InScr.of_frm frame bound) hk
  have px : word t.mem c.B 128 = off c.arena shaped := by simpa only [h.1.arena] using hxp
  have pq : word t.mem c.B 144 = off c.arena q := by simpa only [h.1.arena] using hqp
  have pp : word t.mem c.B 160 = off c.arena p := by simpa only [h.1.arena] using hpp
  have pe : word t.mem c.B 168 = off c.arena exponent := by simpa only [h.1.arena] using hep
  have xl : word t.mem c.B 136 = BitVec.ofNat 64 c.xb.length := by rw [h.2.2.1]; exact hxl
  have ql : word t.mem c.B 152 = BitVec.ofNat 64 c.qb.length := by rw [h.2.2.2]; exact hql
  have outlen : word t.mem c.B 136 = BitVec.ofNat 64 (8 * c.w) := by rw [← c.xLength]; exact xl
  refine ⟨⟨⟨ht, px, xl, sx, ?_, Nat.le_of_eq c.xLength⟩,
    ⟨ht, pq, ql, sq, c.qNonempty, c.qLength⟩, c.qPositive, c.qFits⟩,
    ⟨ht, pp, outlen, hm, ?_, c.pOutside⟩, ⟨ht, pe, outlen, hm, ?_, c.eOutside⟩⟩
  · change 1 ≤ c.xb.length
    omega_using [c.xLength, h.2.1.w1]
  · intro i hi; rw [hk.2.2]; exact h.1.pWrite i hi
  · intro i hi; rw [hk.2.2]; exact h.1.eWrite i hi

theorem candidateFromFrame_ct (pLen qLen : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (candidateArguments pLen qLen))) hc).isSome = true) :
    RelCT isa (Two (CandidateFrameBefore pLen qLen)) (candidateFromFrame pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map CandidateFramePublic.pointers
    (fun _ _ h => ⟨h.2.1.rdi, h.1.stack⟩) (candidateArguments_ct pLen qLen ht))
    (fun _ _ h => candidateFrame_ready h)) ?_
  exact two_map CandidateFramePublic.build (fun _ _ h => h) candidateBuild_ct

end VG.Proof.Dsa.X86_64.Generation
