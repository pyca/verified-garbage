module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Whole
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Pass
import VerifiedGarbage.Proof.AesOcb.PPC64LE.RestTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Whole
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Pass
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.RestTag
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesOcb.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# AES-OCB on PPC64LE: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the public registers (the data's address and length among them)
and, for the rest of the data, its address and length (`r24`, `r25`), which
are the same in both runs; what each piece keeps of them is read off its
instructions (`exec_keep`) or from its correctness proof. The calls have the
same arguments in both runs (`callBlocks_rel`). As on AArch64
(`Proof/AesOcb/AArch64/BodyCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxLstar)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesGcm.PPC64LE (frozen Keeps eval_zero shr4)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_lsr → cwp_lsr

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers, which keeps the others. -/
theorem rel_seqKeep {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : c₁.noCalls = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ ∧ Keep rs σ₁ τ₁ → Env V₂ sp τ₂ ∧ Keep rs σ₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => ⟨E₁.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩)
    (fun _ _ h => ⟨E₂.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩) h₂

/-- The data of the second run, with the first run's registers. -/
theorem Agree.dbuf {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} {n : Nat}
    (h : DBuf (V₂ .r29) (V₂ .r31) s (V₂ .r27) n) : DBuf (V₁ .r29) (V₁ .r31) s (V₁ .r27) n := by
  rw [hV .r29 (by decide), hV .r31 (by decide), hV .r27 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
include L hV hR h28

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (Eq2 σ₁ σ₂) (tag d) TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold tag
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) [.r3, .r4]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  rcases hd with rfl | rfl
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The rest of the data (at `r24`, `r25` bytes), in two runs. -/
theorem rest_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) (rest enc) TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold rest
  refine rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) [.r3, .r4]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  have a₁ : u₁.gpr .r24 = σ₁.gpr .r24 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have a₂ : u₂.gpr .r24 = σ₂.gpr .r24 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  have b₁ : u₁.gpr .r25 = σ₁.gpr .r25 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have b₂ : u₂.gpr .r25 = σ₂.gpr .r25 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.r24, .r25] (by agree_ppc [a₁, a₂, b₁, b₂, h24, h25])
      ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.r24, .r25] (by agree_ppc [a₁, a₂, b₁, b₂, h24, h25])
      ⟨_, by taint_decide⟩

/-- The whole blocks (`n / 16 > 0` of them), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    (nf : c.noFrames = true) {pre post : List Instr} (rs : List Reg)
    (hpre : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) (.seq (.block passStart) (pass pre)) h).isSome = true)
    (hpost : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR))
      (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass post)) h).isSome = true)
    (hk : writesOnly rs (.seq (.block passStart) (pass pre)) = true)
    (hn : (Code.seq (.block passStart) (pass pre) : Prog isa).noCalls = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat} (h23 : V₁ .r23 = BitVec.ofNat 64 n)
    (hD₁ : DBuf (V₁ .r29) (V₁ .r31) σ₁ (V₁ .r27) n) (hD₂ : DBuf (V₂ .r29) (V₂ .r31) σ₂ (V₂ .r27) n) :
    RelCT isa (Eq2 σ₁ σ₂) (whole (.call name c) pre post) TT := by
  have hl := hD₁.lt
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have h23₂ : V₂ .r23 = BitVec.ofNat 64 n := (hV .r23 (by decide)).symm.trans h23
  have e27 := hV .r27 (by decide)
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  unfold whole
  refine RelCT.assoc (rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) hpre) rs hk hn hd
    fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_)
  refine RelCT.assoc (rel_seq (callBlocks_rel L hV ok ct hR h28 F₁ F₂ [] (by agree_ppc []) ⟨_, by taint_decide⟩
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₁.r27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₁.r23, h23]))
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₂.r27, e27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₂.r23, h23₂]))
      (dstD ((hD₁.take' hmn).of_eq K₁.2.1 K₁.2.2)) (dstD ((hV.dbuf (hD₂.take' hmn)).of_eq K₂.2.1 K₂.2.2)))
    (callBlocks_ok L ok nf hR h28 F₁ (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₁.r27])
        hl (by rw [g _ (by decide) (by decide) (by decide), F₁.r23, h23]))
      (dstD ((hD₁.take' hmn).of_eq K₁.2.1 K₁.2.2)))
    (callBlocks_ok (hV.lay L) ok nf hR h28₂ F₂
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₂.r27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₂.r23, h23₂]))
      (dstD ((hD₂.take' hmn).of_eq K₂.2.1 K₂.2.2))) fun u₁ u₂ P₁ P₂ => ?_)
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) hpost

end

/-- `r3 ← n / 16`, the number of whole blocks. -/
theorem bodyHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {n : Nat} (hn : n < 2 ^ 64)
    (h23 : V .r23 = BitVec.ofNat 64 n) :
    WP isa (.block [.lsr .d .r3 .r23 4]) s fun s₁ =>
      s₁.gpr .r3 = BitVec.ofNat 64 (n / 16) ∧ Env V sp s₁ ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
  cwp_lsr (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, E.r23, h23, shr4 hn],
    E.others (rs := [.r3]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr, u₁.rd, u₁.wr⟩

/-- The whole blocks of `seal`, if any: the environment after them. -/
theorem wholeEnv_seal {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole encCall (addCk ++ xorOfs) xorOfs)))
      s fun t => Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29))
    (ckF1 := ckOf fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames hcall_enc sealPre_ok xorOfs_ok L E hR h28 h23 hD
    hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P => ⟨P.env, P.rd, P.wr⟩

/-- The whole blocks of `open`, if any: the environment after them. -/
theorem wholeEnv_open {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole decCall xorOfs (xorOfs ++ addCk))))
      s fun t => Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .r29) (16 * (R + 1)))
      (blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .r29)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .r29)) (i + 1))
    Proof.Aes.PPC64LE.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok openPost_ok L E hR h28 h23 hD
    hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P => ⟨P.env, P.rd, P.wr⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
include L hV hR h28

/-- `body`, in two runs, from what its whole blocks leave in each. -/
theorem body_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat}
    (h23 : V₁ .r23 = BitVec.ofNat 64 n) (hD₁ : DBuf (V₁ .r29) (V₁ .r31) σ₁ (V₁ .r27) n)
    (hD₂ : DBuf (V₂ .r29) (V₂ .r31) σ₂ (V₂ .r27) n)
    (W₁ : WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block [])
      (if enc then whole encCall (addCk ++ xorOfs) xorOfs else whole decCall xorOfs (xorOfs ++ addCk)))) σ₁
      fun t => Env V₁ sp t ∧ t.rd = σ₁.rd ∧ t.wr = σ₁.wr)
    (W₂ : WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block [])
      (if enc then whole encCall (addCk ++ xorOfs) xorOfs else whole decCall xorOfs (xorOfs ++ addCk)))) σ₂
      fun t => Env V₂ sp t ∧ t.rd = σ₂.rd ∧ t.wr = σ₂.wr) :
    RelCT isa (Eq2 σ₁ σ₂) (body enc) TT := by
  have hn := hD₁.lt
  have h23₂ : V₂ .r23 = BitVec.ofNat 64 n := (hV .r23 (by decide)).symm.trans h23
  unfold body
  refine RelCT.assoc (rel_seq ?_ W₁ W₂ fun τ₁ τ₂ ⟨F₁, _⟩ ⟨F₂, _⟩ => ?_)
  · refine rel_seq (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (bodyHead_ok E₁ hn h23)
      (bodyHead_ok E₂ hn h23₂) fun u₁ u₂ ⟨r3₁, U₁, rd₁, wr₁⟩ ⟨r3₂, U₂, rd₂, wr₂⟩ => ?_
    refine rel_ite (eval_zero r3₁ (by omega)) (eval_zero r3₂ (by omega)) (fun _ => rel_skip) fun _ => ?_
    cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact whole_rel L hV hR h28 Proof.Aes.PPC64LE.decryptBlocks_correct Proof.Aes.PPC64LE.decryptBlocks_ct
        decryptBlocks_noFrames [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26] ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩ (by decide +kernel) (by decide +kernel) (by decide) U₁ U₂ h23
        (hD₁.of_eq rd₁ wr₁) (hD₂.of_eq rd₂ wr₂)
    · exact whole_rel L hV hR h28 Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct
        encryptBlocks_noFrames [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26] ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩ (by decide +kernel) (by decide +kernel) (by decide) U₁ U₂ h23
        (hD₁.of_eq rd₁ wr₁) (hD₂.of_eq rd₂ wr₂)
  refine rel_seq (rel_env F₁ F₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (bodyTail_ok F₁ hn h23)
    (bodyTail_ok F₂ hn h23₂) fun w₁ w₂ ⟨r24₁, r25₁, g₁, k₁⟩ ⟨r24₂, r25₂, g₂, k₂⟩ => ?_
  exact rel_ite (eval_zero r25₁ (by omega)) (eval_zero r25₂ (by omega)) (fun _ => rel_skip) fun _ =>
    rest_rel L hV hR h28 enc (F₁.others g₁ k₁.sp k₁.rd k₁.wr) (F₂.others g₂ k₂.sp k₂.rd k₂.wr)
      (by rw [r24₁, r24₂, hV .r27 (by decide)]) (by rw [r25₁, r25₂])

end

end VG.Proof.AesOcb.PPC64LE
