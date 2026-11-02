module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Block

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: correctness

`code_ok`: from the precondition, `signC` keeps the calling convention, and
`out` and the result are as `RsaPss.sign` says (`Post`): the prologue
(`prologue_ok`), the check of the modulus' first byte, `emBits` and
`encode`'s arguments (`emBitsB_ok`, `encArgs_ok`), the call of `encode`
(`encCall_ok`), then either zeros to `out` (`fail_ok`) or the private-key
operation on `EM` (`privArgs_ok`, `call_ok`), and the restores
(`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.RsaPss.AArch64 (off EncImpl ebV emBitsB_ok restore_frame_ok)

/-- Signing's result, and the calling convention. -/
def Post (G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32) (signOut G s)

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  simp [eval, State.read]

/-- `emBits`, `emLen` and `lo` of a call from `s`. -/
abbrev ebS (s : State) : Nat := ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat
abbrev elS (s : State) : Nat := Spec.RsaPss.emLength (ebS s)
abbrev loS (s : State) : Nat := (s.gpr .x3).toNat - elS s

section
variable {D K : Nat} {s : State} (hp : PreS D K s) (h0 : s.mem (s.gpr .x2) ≠ 0)
include hp h0

theorem eb_bounds : 1 ≤ ebS s ∧ ebS s ≤ Proof.RsaPss.maxEmBits ∧ loS s + elS s = (s.gpr .x3).toNat ∧ loS s ≤ 1 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have h0' : (s.mem (s.gpr .x2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hl8 := RsaPss.log2_lt8 (s.mem (s.gpr .x2))
  unfold loS elS ebS Spec.RsaPss.emLength ebV Proof.RsaPss.maxEmBits
  omega

/-- `emBits`, `emLen` and `lo`, and `encode`'s arguments. -/
theorem args_ok {u : State} (hu : AtChk s u) :
    WP isa (.block (emBitsB ++ encArgs)) u (AtEnc K s (ebS s) (elS s) (loS s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hx := (s.mem (s.gpr .x2)).isLt
  have h0' : (s.mem (s.gpr .x2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok (by omega) hk2 hx h0' hx10 (by rw [hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
    fun u₁ ⟨O₁, x24, x25, x26⟩ => ?_
  have hpar : AtPar K s (ebS s) (elS s) (loS s) u₁ := {
    sp := O₁.sp.trans hu.sp
    rd := O₁.rd.trans hu.rd
    wr := O₁.wr.trans hu.wr
    v := fun r hr => (O₁.vcs r hr).trans (hu.v r hr)
    mem := by rw [O₁.mem]; exact hu.mem.mono (by simp)
    fr := by rw [O₁.mem]; exact hu.fr
    x20 := (O₁.get .x20).trans hu.x20
    x23 := (O₁.get .x23).trans hu.x23
    x24 := x24
    x25 := x25
    x26 := x26 }
  exact encArgs_ok hp hpar

end

/-- After `encode` returned nonzero: its encoding, after `lo` zero bytes, is
`EM`. -/
theorem main_of {G : Spec.Mgf1.Hash} {K : Nat} {s t : State} (hp : PreS G.len K s) (h0 : s.mem (s.gpr .x2) ≠ 0)
    (ht : AfterEnc G K s (ebS s) (elS s) (loS s) t) (hb : isa.eval (.zero .w .x0) t = some false) :
    ∃ e', Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) (ebS s) = some e' ∧
      Main K s (Spec.RsaPss.zeros (loS s) ++ e') t := by
  obtain ⟨-, -, hlok, hlo⟩ := eb_bounds hp h0
  rw [eval_zero_w] at hb
  have hres := ht.res
  revert hres
  cases Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) (ebS s) with
  | none => intro hres; rw [hres] at hb; exact absurd hb (by decide)
  | some e' =>
    intro hres
    exact ⟨e', rfl, ht.sp, ht.rd, ht.wr, ht.x20, ht.x23, ht.v, ht.mem, ht.fr,
      em_input hlok hlo ht.z hres.2⟩

section
variable {G : Spec.Mgf1.Hash} (e : EncImpl G) (c : PrivChecked) {K : Nat} (heK : e.stack ≤ K) (hcK : c.stack ≤ K)

include heK hcK in
/-- After the check of the modulus' first byte: the encoding, then the
private-key operation or zeros. -/
theorem main_ok {s u : State} (hp : PreS G.len K s) (hu : AtChk s u) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ encArgs), .call e.name e.code,
      .ite (.zero .w .x0) signFail (.seq (.block privArgs) (.call c.name c.code))]) u fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut G s) := by
  have hk1 := hp.k1
  obtain ⟨heb1, heb2, hlok, -⟩ := eb_bounds hp h0
  have hsign := signOut_enc G (s := s) (by omega) h0
  unfold seqs seqs
  refine WP.seq (WP.mono (args_ok hp h0 hu) fun t ht => ?_)
  refine WP.seq (WP.mono (encCall_ok e hp heK ht (by omega) rfl heb1 heb2) fun t₂ ht₂ => ?_)
  have M₂ : Mid s t₂ := ⟨ht₂.sp, ht₂.rd, ht₂.wr, ht₂.v, ht₂.fr⟩
  refine WP.ite _ (eval_zero_w _ _) (fun hb => ?_) (fun hb => ?_)
  · -- No encoding: zeros.
    refine WP.mono (fail_ok hp M₂ ht₂.x23) fun t' ⟨m, r⟩ => ⟨m, ?_⟩
    rw [hsign]
    have hres := ht₂.res
    revert hres
    cases Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) (ebS s) with
    | none => intro _; exact r
    | some e' =>
      intro hres
      rw [hres.1] at hb
      exact absurd hb (by decide)
  -- The encoding, and the private-key operation.
  obtain ⟨e', he', hm⟩ := main_of hp h0 ht₂ (by rw [eval_zero_w, ← hb])
  refine WP.seq (WP.mono (privArgs_ok hp hm) fun u₃ h₃ => ?_)
  refine WP.mono (call_ok c hp hcK h₃) fun t' ht' => ⟨ht'.toMid, ?_⟩
  rw [hsign]
  erw [he']
  exact ht'.res

include heK hcK in
/-- After the prologue: the check of the modulus' first byte, then zeros or
`main_ok`. -/
theorem body_ok {s u : State} (hp : PreS G.len K s) (hu : AtChk s u) :
    WP isa (.ite (.zero .x .x10) signFail (seqs [.block (emBitsB ++ encArgs), .call e.name e.code,
      .ite (.zero .w .x0) signFail (.seq (.block privArgs) (.call c.name c.code))])) u fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut G s) := by
  have hk1 := hp.k1
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`.
    have h0 : s.mem (s.gpr .x2) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x2)).isLt; omega)] at this
      exact this
    exact WP.mono (fail_ok hp ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩ hu.x23) fun t ⟨m, r⟩ =>
      ⟨m, by rw [signOut_zero G (by omega) h0]; exact r⟩
  have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact main_ok e c heK hcK hp hu h0

include heK hcK in
theorem code_ok {s : State} (hp : PreS G.len K s) :
    WP isa (signC e.name e.code c.name c.code) s (Post G s) := by
  unfold signC
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega) ?_
  unfold signCBody seqs seqs seqs
  refine WP.seq (WP.mono (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (body_ok e c heK hcK hp hu) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, hmem⟩ =>
    ⟨habi, by rw [hx0, hmem]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Sgn
