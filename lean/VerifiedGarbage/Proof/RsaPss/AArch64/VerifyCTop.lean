module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyChk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: correctness

`code_ok`: from the precondition, `verifyC` keeps the calling convention,
and, if `pre` holds the modulus' values, returns 1 exactly when
`RsaPss.verify` says (`Post`): the prologue (`prologue_ok`), the check of
the modulus' first byte, `emBits` and the public operation's arguments
(`emBitsB_ok`, `pubArgs_ok`), its call (`call_ok`), `checkEncoding`'s
arguments and its call for the index of the table of `MdHash` (`chkArgs_ok`,
`byIdx_wp`, `chkCall_ok`), and the result's AND with the leading byte's
check (`verifyOut_enc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (wp_nil wp_and wp_movz eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.AArch64 (off emBitsB_ok restore_frame_ok byIdx_wp Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb frame_sub frame_sub0 setWidth_byte)

/-- Verifying's result, if `pre` holds the modulus' values, and the calling
convention. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (Cons s → (s'.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0)

/-- Before the checks. -/
theorem fail_ok {s t : State} (hm : Mid s t) :
    WP isa verifyFail t fun t' => Mid s t' ∧ (t'.gpr .x0).setWidth 32 = 0 := by
  unfold verifyFail movi
  exact wp_movz fun w o e => wp_nil ⟨⟨by rw [o.sp, hm.sp], by rw [o.rd, hm.rd], by rw [o.wr, hm.wr],
    fun r hr => by rw [o.vcs r hr, hm.v r hr], by rw [o.mem]; exact hm.fr⟩, by rw [e]; rfl⟩

theorem and_flags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then (1 : BitVec 32) else 0) &&& (if q then (1 : BitVec 64) else 0).setWidth 32) =
      if q ∧ p then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `emBits`, `emLen` and `lo`, and the public operation's arguments. -/
theorem pubArgsC_ok {tsH tsG : List FnTable} {K : Nat} {s u : State} (hp : PreV tsH tsG K s) (hu : AtChk s u) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    WP isa (.block (emBitsB ++ pubArgsC)) u (AtCall s (ebS s) (elS s) (loS s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hx := (s.mem (s.gpr .x0)).isLt
  have h0' : (s.mem (s.gpr .x0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x0)).toNat := by rw [hu.x10, setWidth_byte]
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok (by omega) hk2 hx h0' hx10 (by rw [hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
    fun u₁ ⟨O₁, x24, x25, x26⟩ => ?_
  have hpc : PreCall s (ebS s) (elS s) (loS s) u₁ := {
    sp := O₁.sp.trans hu.sp
    rd := O₁.rd.trans hu.rd
    wr := O₁.wr.trans hu.wr
    x20 := (O₁.get .x20).trans hu.x20
    x23 := (O₁.get .x23).trans hu.x23
    x24 := x24
    x25 := x25
    x26 := x26
    x27 := (O₁.get .x27).trans hu.x27
    v := fun r hr => (O₁.vcs r hr).trans (hu.v r hr)
    mem := by rw [O₁.mem]; exact hu.mem
    fr := by rw [O₁.mem]; exact hu.fr }
  exact pubArgs_ok hpc

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PdChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include h624 hcK in
/-- After the check of the modulus' first byte: the public operation, the
check of the encoding, and the AND. -/
theorem main_ok {s u : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code, .block chkArgs,
      byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs,
      .block [.logic .and .x .x0 .x0 .x26]]) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, -, hlo⟩ := eb_bounds hk1 hk2 h0
  unfold seqs seqs seqs seqs
  refine WP.seq (WP.mono_syms (pubArgsC_ok hp hu h0) fun t ht sy => ?_)
  refine WP.seq (WP.mono_syms (call_ok c hp hcK ht) fun t₂ ht₂ sy₂ => ?_)
  refine WP.seq (WP.mono_syms (chkArgs_ok hp h0 ht₂) fun t₃ ht₃ sy₃ => ?_)
  refine WP.seq (byIdx_wp E.mem (fun j hj => by unfold idxs at hj; simp at hj; omega) (ht₃.x27.trans E.idx)
    fun t' o sy' => WP.mono (chkCall_ok hp h624 E h0 (ht₃.only9 o) (by rw [sy', sy₃, sy₂, sy, hsy]))
      fun t₄ ht₄ => ?_)
  refine wp_and fun t₅ o₅ e₅ => wp_nil ⟨⟨by rw [o₅.sp, ht₄.sp], by rw [o₅.rd, ht₄.rd], by rw [o₅.wr, ht₄.wr],
    fun r hr => by rw [o₅.vcs r hr, ht₄.v r hr], by rw [o₅.mem]; exact ht₄.fr⟩, fun hc => ?_⟩
  rw [e₅, BitVec.setWidth_and, ht₄.x0 hc, ht₄.x26 hc, and_flags, verifyOut_enc Hs Gs hk1 hk2 h0,
    take_zeros hlo (by rw [pubX_length]; omega)]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

include h624 hcK in
/-- After the prologue: the check of the modulus' first byte, then 0 or
`main_ok`. -/
theorem body_ok {s u : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) :
    WP isa (.ite (.zero .x .x10) verifyFail (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code,
      .block chkArgs, byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs,
      .block [.logic .and .x .x0 .x0 .x26]])) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0) := by
  have hk1 := hp.k1
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x0)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have h0 : s.mem (s.gpr .x0) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x0)).isLt; omega)] at this
      exact this
    exact WP.mono (fail_ok ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩) fun t ⟨m, r⟩ =>
      ⟨m, fun _ => by rw [verifyOut_zero Hs Gs (by omega) h0, r]; rfl⟩
  have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact main_ok c h624 hcK hp E hu hsy h0

include h624 hcK in
theorem code_ok {s : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) :
    WP isa (verifyC f g c.name c.code) s (Post Hs Gs s) := by
  unfold verifyC
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega) ?_
  unfold verifyCBody seqs seqs seqs
  refine WP.seq (WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_)
  refine WP.seq (WP.mono (body_ok c h624 hcK hp E hu (by rw [sy]; simp [allocated])) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ =>
    ⟨habi, fun hc => by rw [hx0]; exact r hc⟩

end

end VG.Proof.RsaPss.AArch64.Vfy
