module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerSave
import VerifiedGarbage.Proof.Framework.Omega

/-! # Restore the workspace and turn the shared result into RSA's mask -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

private theorem low_result {v : BitVec 64} {p : Bool}
    (h : (v.setWidth 32).toNat = if p then 1 else 0) :
    v.setWidth 32 = BitVec.ofNat 32 p.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases p <;> simpa using h

private theorem negative_result (p : Bool) :
    BitVec.signExtend 64 (0 : BitVec 32) - (BitVec.ofNat 32 p.toNat).setWidth 64 = mask p := by
  cases p <;> decide

private theorem imul_low (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

theorem restore_ok {s : State} {B old : Addr} {Z w : Nat} {p : Bool}
    (h : Scr s B Z) (hZ : slot w 28 ≤ Z) (hB : s.gpr .rbx = B)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hv : word s.mem B (pad w) = old)
    (hr : ((s.gpr .rax).setWidth 32).toNat = if p then 1 else 0) :
    WP isa (.block restore) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kFlag)) (mask p) ∧ t.gpr .rdi = B ∧ t.gpr .rbx = old ∧
      Keep [.rax, .rbx, .rcx, .rdi] s t := by
  have hf : InRegions s.wr (off B (8 * kFlag)) 8 :=
    h.st (by have := hdr_lt_slot w 28 (show kFlag < 32 by decide); omega_arith)
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    h.ld (by have := hdr_lt_slot w 28 (show sW < 32 by decide); omega_arith)
  have hp : pad w + 8 ≤ Z := by
    simp only [pad, slot, hdrBytes, aR1] at hZ ⊢
    omega_arith
  have hpL : InRegions (s.rd ++ s.wr) (off B (pad w)) 8 := h.ld hp
  let m := s.mem.writeW (off B (8 * kFlag)) (mask p)
  have ho : Outside B (8 * kFlag) 8 s.mem m := writeW_outside _ _ _ (by decide)
  have hmw : word m B (8 * sW) = BitVec.ofNat 64 w :=
    (ho.word (Or.inl (by decide)) (by decide)).trans hw
  have hmp : word m B (pad w) = old :=
    (ho.word (Or.inr (by simp only [pad, slot, hdrBytes, aR1, kFlag, kPlen, sFn]; omega_arith))
      (by have := h.nowrap; omega_arith)).trans hv
  dsimp only [m, VG.Proof.Bignum.word] at hmw hmp
  have ha : BitVec.signExtend 64 (208 : BitVec 32) * BitVec.ofNat 64 w +
      BitVec.signExtend 64 (656 : BitVec 32) + B = off B (pad w) := by
    change 208#64 * BitVec.ofNat 64 w + 656#64 + B = off B (pad w)
    simp only [pad, slot, hdrBytes, aR1, off]
    bv_omega
  have hb := low_result hr
  have hm := negative_result p
  refine WP.mono (WP.keep [.rax, .rbx, .rcx, .rdi] (c := .block restore)
    (Q := fun t => t.mem = m ∧ t.gpr .rdi = B ∧ t.gpr .rbx = old) ?_ rfl)
    fun t ⟨⟨hmem, hdi, hbx⟩, hk⟩ => ⟨hmem, hdi, hbx, hk⟩
  unfold restore padAddress
  simp only [List.cons_append, List.nil_append]
  xrun [execImul, imul_low, BitVec.add_zero,
    show BitVec.signExtend 64 (208#32) = 208#64 from rfl,
    show BitVec.signExtend 64 (656#32) = 656#64 from rfl,
    show BitVec.signExtend 64 (28#32) = 28#64 from rfl,
    show BitVec.signExtend 64 (88#32) = 88#64 from rfl,
    show BitVec.ofInt 64 0 = 0#64 from rfl, State.ea, hdr, hdrOff, at0, hB, hb, hm, hf, hl, hpL, ha,
    hmw, hmp]
  rfl

end VG.Proof.MillerRabin.X86_64.Caller
