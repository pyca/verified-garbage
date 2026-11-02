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

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: correctness

`code_ok`: from the precondition, `verifyC` keeps the calling convention,
and, if `pre` holds the modulus' values, returns 1 exactly when
`RsaPss.verify` says (`Post`): the prologue (`prologue_ok`), the check of
the modulus' first byte, `emBits` and the public operation's arguments
(`emBitsB_ok`, `pubArgs_ok`), its call (`call_ok`), `checkEncoding`'s
arguments and call (`chkArgs_ok`, `chk_ok`), and the result's AND with the
leading byte's check (`verifyOut_enc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (wp_nil wp_and wp_movz eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.AArch64 (off ChkImpl chkCall emBitsB_ok restore_frame_ok)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb frame_sub frame_sub0 setWidth_byte)

/-- Verifying's result, if `pre` holds the modulus' values, and the calling
convention. -/
def Post (G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (Cons s → (s'.gpr .x0).setWidth 32 = if verifyOut G s then 1 else 0)

/-- Before the checks. -/
theorem fail_ok {s t : State} (hm : Mid s t) :
    WP isa verifyFail t fun t' => Mid s t' ∧ (t'.gpr .x0).setWidth 32 = 0 := by
  unfold verifyFail movi
  exact wp_movz fun w o e => wp_nil ⟨⟨by rw [o.sp, hm.sp], by rw [o.rd, hm.rd], by rw [o.wr, hm.wr],
    fun r hr => by rw [o.vcs r hr, hm.v r hr], by rw [o.mem]; exact hm.fr⟩, by rw [e]; rfl⟩

theorem bytesAt_drop (m : Mem) (p : Addr) {k lo : Nat} :
    (Spec.Rsa.bytesAt m p k).drop lo = Spec.Rsa.bytesAt m (off p lo) (k - lo) := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range, off, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

theorem and_flags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then (1 : BitVec 32) else 0) &&& (if q then (1 : BitVec 64) else 0).setWidth 32) =
      if q ∧ p then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- After `checkEncoding`. -/
structure AfterChk (G : Spec.Mgf1.Hash) (s t : State) : Prop extends Mid s t where
  x26 : Cons s → t.gpr .x26 = if loS s = 0 ∨ (pubX s).getD 0 0 = 0 then 1 else 0
  x0 : Cons s → (t.gpr .x0).setWidth 32 = if Spec.RsaPss.verifyEncoding G G
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len) ((pubX s).drop (loS s)) (ebS s) (sLenV s) then 1 else 0

theorem chk_ok {G : Spec.Mgf1.Hash} (e : ChkImpl G) {K : Nat} {s t : State} (hp : PreV G.len K s)
    (heK : e.stack ≤ K) (h0 : s.mem (s.gpr .x0) ≠ 0) (ht : AtChkC K s t) :
    WP isa (.call e.name e.code) t (AfterChk G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, hlok, -⟩ := eb_bounds hk1 hk2 h0
  have hfb := fb_toNat hp
  have hd := e.depth
  have hcl := e.le
  have hcw : (s.gpr .x1).toNat ≤ 8 * cwV s := by unfold cwV; omega
  have hsc := cw_toNat hp
  have hhs := hp.hs
  refine chkCall e (chkOk_of hp heK h0 ht) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [VG.Proof.RsaPss.AArch64.chkWr] at hf
  rw [ht.x6, ht.x7, ht.sp] at hf
  have hSsc : Region.Sub ⟨off (scr s) (8 * cwV s), (stackArg s 2 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold cwV at *; omega)
  have hA : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [(⟨off (scr s) (8 * cwV s),
      (stackArg s 2 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ : Region)] ++ [below (fb s) (16 * e.code.aarch64Depth)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right hSsc
    · exact Offset.disjoint_below _ (by unfold frameBytes at hdn; omega)
  have hx4 : Spec.RsaPss.expectedSaltLen (t.gpr .x4) ((t.gpr .x5).setWidth 32) = sLenV s := by
    rw [ht.x4, ht.x5, ← expected_eq]
    congr 1
    unfold anyV
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  have hdg : Spec.Rsa.bytesAt t.mem (s.gpr .x4) G.len = Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ht.mem.bytes (R := ⟨s.gpr .x4, G.len⟩) (fun r hr => ?_)
      (by show G.len ≤ 2 ^ 64; have := hp.wdg; omega) (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.kdg.symm
    · exact hp.dgs
  exact {
    sp := hsp'.trans ht.sp
    rd := hrd'.trans ht.rd
    wr := hwr'.trans ht.wr
    v := fun r hr => (hvs r hr).trans (ht.v r hr)
    fr := ht.fr.frame hf (hA (by decide)) (hA (by decide)) (hA (by decide))
    x26 := fun hc => by
      rw [hpres .x26 (by decide) (by decide), ht.x26]
      have hb := ht.res hc
      have e0 : t.mem (scr s) = (pubX s).getD 0 0 := by
        rw [← hb, Sgn.bytesAt_cons _ _ (by omega)]; rfl
      rw [e0]
    x0 := fun hc => by
      obtain ⟨-, hb2, -, -⟩ := eb_bounds hk1 hk2 h0
      have he : (BitVec.ofNat 64 (elS s)).toNat = elS s := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show elS s < 2 ^ 64 by omega)]
      have hb : (BitVec.ofNat 64 (ebS s)).toNat = ebS s := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ebS s < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
      rw [hpost, ht.x0, ht.x1, ht.x2, ht.x3, hx4, hdg, he, hb, ← ht.res hc, bytesAt_drop,
        show (s.gpr .x1).toNat - loS s = elS s by omega] }

/-- `emBits`, `emLen` and `lo`, and the public operation's arguments. -/
theorem pubArgsC_ok {D K : Nat} {s u : State} (hp : PreV D K s) (hu : AtChk s u) (h0 : s.mem (s.gpr .x0) ≠ 0) :
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
    v := fun r hr => (O₁.vcs r hr).trans (hu.v r hr)
    mem := by rw [O₁.mem]; exact hu.mem
    fr := by rw [O₁.mem]; exact hu.fr }
  exact pubArgs_ok hpc

section
variable {G : Spec.Mgf1.Hash} (c : PdChecked) (e : ChkImpl G) {K : Nat} (hcK : c.stack ≤ K) (heK : e.stack ≤ K)

include hcK heK in
/-- After the check of the modulus' first byte: the public operation, the
check of the encoding, and the AND. -/
theorem main_ok {s u : State} (hp : PreV G.len K s) (hu : AtChk s u) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code, .block chkArgs, .call e.name e.code,
      .block [.logic .and .x .x0 .x0 .x26]]) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut G s then 1 else 0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, -, hlo⟩ := eb_bounds hk1 hk2 h0
  unfold seqs seqs seqs seqs
  refine WP.seq (WP.mono (pubArgsC_ok hp hu h0) fun t ht => ?_)
  refine WP.seq (WP.mono (call_ok c hp hcK ht) fun t₂ ht₂ => ?_)
  refine WP.seq (WP.mono (chkArgs_ok hp h0 ht₂) fun t₃ ht₃ => ?_)
  refine WP.seq (WP.mono (chk_ok e hp heK h0 ht₃) fun t₄ ht₄ => ?_)
  refine wp_and fun t₅ o₅ e₅ => wp_nil ⟨⟨by rw [o₅.sp, ht₄.sp], by rw [o₅.rd, ht₄.rd], by rw [o₅.wr, ht₄.wr],
    fun r hr => by rw [o₅.vcs r hr, ht₄.v r hr], by rw [o₅.mem]; exact ht₄.fr⟩, fun hc => ?_⟩
  rw [e₅, BitVec.setWidth_and, ht₄.x0 hc, ht₄.x26 hc, and_flags, verifyOut_enc G hk1 hk2 h0,
    take_zeros hlo (by rw [pubX_length]; omega)]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

include hcK heK in
/-- After the prologue: the check of the modulus' first byte, then 0 or
`main_ok`. -/
theorem body_ok {s u : State} (hp : PreV G.len K s) (hu : AtChk s u) :
    WP isa (.ite (.zero .x .x10) verifyFail (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code,
      .block chkArgs, .call e.name e.code, .block [.logic .and .x .x0 .x0 .x26]])) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut G s then 1 else 0) := by
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
      ⟨m, fun _ => by rw [verifyOut_zero G (by omega) h0, r]; rfl⟩
  have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact main_ok c e hcK heK hp hu h0

include hcK heK in
theorem code_ok {s : State} (hp : PreV G.len K s) :
    WP isa (verifyC e.name e.code c.name c.code) s (Post G s) := by
  unfold verifyC
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega) ?_
  unfold verifyCBody seqs seqs seqs
  refine WP.seq (WP.mono (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (body_ok c e hcK heK hp hu) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ =>
    ⟨habi, fun hc => by rw [hx0]; exact r hc⟩

end

end VG.Proof.RsaPss.AArch64.Vfy
