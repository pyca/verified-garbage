module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashChunk
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashChunk
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesOcb.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# AES-OCB on PPC64LE: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`. The counts of blocks a
chunk loads from `W` (the blocks left, at `W + hlO`, and the chunk's, at
`W + cnO`), which the taint analysis takes as secret, are the same in both
runs by the correctness proofs (`HInv`, `FillInv`), which also pin the
pointer `r24` and the index `r26`: the blocks are split after each load
(`chunkLd_ok`, `sumArgs_ok`). Each chunk fills its buffer and adds it to the
sum by code the taint analysis checks, with the call between on the same
arguments (`chunk_rel`); both runs are at the same chunk at each iteration
(`hashLoop_rel`); the rest, if any, likewise (`hashRest_rel`). As on AArch64
(`Proof/AesOcb/AArch64/HashCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Ocb (Block Cipher)
open VG.Proof.AesGcm.PPC64LE (frozen Keeps eval_zero)

/-- An environment, after code that writes only `a` and `b` among the registers. -/
theorem Env.keep2 {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (E : Env V sp s) {a b : Reg}
    (g : ∀ r, r ≠ a → r ≠ b → s'.gpr r = s.gpr r) (k : Keeps s s') (ha : a ∉ frozen := by decide)
    (hb : b ∉ frozen := by decide) : Env V sp s' :=
  E.keep (fun r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr))) k.sp k.rd k.wr

/-- An environment, after code that writes only `a`, `b` and `c` among the registers. -/
theorem Env.keep3 {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (E : Env V sp s) {a b c : Reg}
    (g : ∀ r, r ≠ a → r ≠ b → r ≠ c → s'.gpr r = s.gpr r) (k : Keeps s s') (ha : a ∉ frozen := by decide)
    (hb : b ∉ frozen := by decide) (hc : c ∉ frozen := by decide) : Env V sp s' :=
  E.keep (fun r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr)) (fun h => hc (h ▸ hr))) k.sp k.rd k.wr

/-- What the second run may access, with the first run's key context and `W`. -/
theorem Agree.perm {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} (h : Perm (V₂ .r29) (V₂ .r31) s) :
    Perm (V₁ .r29) (V₁ .r31) s := by
  rw [hV .r29 (by decide), hV .r31 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (hV : Agree V₁ V₂)
include hV

/-- The rest of the associated data, in two runs from the same `r24` and `r25`. -/
theorem hashRest_rel (L : Lay (V₁ .r29) (V₁ .r31)) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) hashRest TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.r24, .r25] (by agree_ppc [h24, h25])
    ⟨_, by taint_decide⟩) [.r0, .r3, .r4, .r5, .r6] (by decide +kernel) (by decide +kernel) (by decide)
    fun τ₁ τ₂ F₁ F₂ => ?_))
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

variable {D : Addr} {n R : Nat} {A : Addr} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte}
  {s₁ s₂ : State} (C₁ : HCtx (V₁ .r29) (V₁ .r31) D n R ciph₁ l₁ A a₁ s₁)
  (C₂ : HCtx (V₂ .r29) (V₂ .r31) D n R ciph₂ l₂ A a₂ s₂) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
  (hlen : a₂.length = a₁.length)
include C₁ C₂ h28 hlen

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel {τ₁ τ₂ : State} {j : Nat} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ j)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ j) (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hs := C₁.short
  have L := C₁.lay
  have e31 := hV .r31 (by decide)
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have hl₂ := H₂.hl
  rw [hlen] at hl₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq ?_ (chunkHead_ok (L := a₁.length / 16 - j) H₁.env.r31 H₁.env.perm.w (by omega_arith) H₁.hl)
    (chunkHead_ok (L := a₁.length / 16 - j) H₂.env.r31 H₂.env.perm.w (by omega_arith) hl₂)
    fun t₁ t₂ ⟨h25₁, g₁, k₁⟩ ⟨h25₂, g₂, k₂⟩ => ?_)
  · -- the number of blocks of the chunk, from those left
    refine rel_seq (rel_env H₁.env H₂.env hV [] (by agree_ppc []) ⟨_, by taint_decide⟩)
      (chunkLd_ok (L := a₁.length / 16 - j) H₁.env.r31 H₁.env.perm.w (by omega_arith) H₁.hl)
      (chunkLd_ok (L := a₁.length / 16 - j) H₂.env.r31 H₂.env.perm.w (by omega_arith) hl₂)
      fun u₁ u₂ ⟨r3₁, r4₁, _, k₁⟩ ⟨r3₂, r4₂, _, k₂⟩ => ?_
    have hsp : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, H₁.env.sp, H₂.env.sp]
    refine rel_ite (eval_zero r4₁ (by omega_arith)) (eval_zero r4₂ (by omega_arith)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_taint [.r3] hsp (by agree_ppc [r3₁, r3₂]) ⟨_, by taint_decide⟩
    · exact rel_taint [] hsp (by agree_ppc []) ⟨_, by taint_decide⟩
  have E₁ := H₁.env.keep3 g₁ k₁
  have E₂ := H₂.env.keep3 g₂ k₂
  -- the counts stored
  refine rel_seq (rel_env E₁ E₂ hV [.r25] (by agree_ppc [h25₁, h25₂]) ⟨_, by taint_decide⟩)
    (chunkMid_ok C₁ H₁ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₁ k₁ h25₁)
    (chunkMid_ok C₂ H₂ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₂ k₂ h25₂) fun w₁ w₂ F₁ F₂ => ?_
  -- the buffer filled
  refine rel_seq (rel_env F₁.env F₂.env hV [.r11, .r24, .r25, .r26]
      (by agree_ppc [F₁.r11, F₂.r11, F₁.r24, F₂.r24, F₁.r25, F₂.r25, F₁.r26, F₂.r26, e31]) ⟨_, by taint_decide⟩)
    (fill_ok C₁ (by omega_arith) (by omega_arith) (by omega_arith) F₁) (fill_ok C₂ (by omega_arith) (by omega_arith) (by omega_arith) F₂)
    fun y₁ y₂ G₁ G₂ => ?_
  -- enciphered
  let c := min 8 (a₁.length / 16 - j)
  refine RelCT.assoc (rel_seq (F₁ := fun z => Env V₁ sp z ∧
      z.mem.readW (V₁ .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (F₂ := fun z => Env V₂ sp z ∧ z.mem.readW (V₂ .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (callBlocks_rel L hV Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct C₁.rounds h28 G₁.env G₂.env [] (by agree_ppc []) ⟨_, by taint_decide⟩
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₁.env.r31])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₂.env.r31, e31])
        (by rw [k.wr, e31]; exact G₂.env.perm.w) (by rw [k.mem, e31, G₂.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))
      (dstW L (hV.perm G₂.env.perm) (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames
      C₁.rounds h28 G₁.env
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₁.env.r31])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₁.env, (bufCall_readW L P (by omega_arith) (d := cnO) (by decide)).trans G₁.cn⟩)
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (hV.lay L) Proof.Aes.PPC64LE.encryptBlocks_correct
      encryptBlocks_noFrames C₁.rounds h28₂ G₂.env
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₂.env.r31])
        (by rw [k.wr]; exact G₂.env.perm.w) (by rw [k.mem, G₂.cn]))
      (dstW (hV.lay L) G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₂.env, (bufCall_readW (hV.lay L) P (by omega_arith) (d := cnO) (by decide)).trans G₂.cn⟩)
    fun z₁ z₂ ⟨Z₁, cn₁⟩ ⟨Z₂, cn₂⟩ => ?_)
  -- the buffer added to the sum
  refine rel_seq (rel_env Z₁ Z₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩)
    (sumArgs_ok Z₁.r31 Z₁.perm.w cn₁) (sumArgs_ok Z₂.r31 Z₂.perm.w cn₂)
    fun x₁ x₂ ⟨r11₁, r25₁, g₁', k₁'⟩ ⟨r11₂, r25₂, g₂', k₂'⟩ => ?_
  have X₁ := Z₁.keep2 g₁' k₁'
  have X₂ := Z₂.keep2 g₂' k₂'
  refine rel_seqEnv X₁ X₂ (rel_env X₁ X₂ hV [.r11, .r25] (by agree_ppc [r11₁, r11₂, r25₁, r25₂, e31])
    ⟨_, by taint_decide⟩) sumRegs (by decide +kernel) (by decide +kernel) (by decide) fun _ _ e₁ e₂ => ?_
  exact rel_env e₁ e₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel {τ₁ τ₂ : State} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ 0)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ 0) (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop hashChunk (.nonzero .d .r3)) TT := by
  have hs := C₁.short
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv V₁ sp ciph₁ l₁ A a₁ s₁ u₁ j ∧ HInv V₂ sp ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((chunk_rel hV C₁ C₂ h28 hlen G₁ G₂ hj).wp
    (F₁ := fun u => HInv V₁ sp ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => HInv V₂ sp ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hashChunk_ok C₁ h28 G₁ hj, hashChunk_ok C₂ h28₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.r3 (by omega_arith)
  have r3₂ := F₂.r3
  rw [hlen] at r3₂
  have ev₂ := eval_nonzero r3₂ (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega_arith, j + min 8 (a₁.length / 16 - j), rfl,
    by omega_arith, F₁, F₂⟩

/-- `HASH`, in two runs. -/
theorem hash_rel (E₁ : Env V₁ sp s₁) (E₂ : Env V₂ sp s₂) (h21 : V₁ .r21 = A)
    (h22 : V₁ .r22 = BitVec.ofNat 64 a₁.length)
    (hl0₁ : Spec.Ocb.blockAtMem s₁.mem (V₁ .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₁ 0)
    (hl0₂ : Spec.Ocb.blockAtMem s₂.mem (V₂ .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) Impl.AesOcb.PPC64LE.hash TT := by
  have hs := C₁.short
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have h21₂ : V₂ .r21 = A := (hV .r21 (by decide)).symm.trans h21
  have h22₂ : V₂ .r22 = BitVec.ofNat 64 a₂.length := by rw [← hV .r22 (by decide), h22, hlen]
  unfold Impl.AesOcb.PPC64LE.hash
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (hashHead_ok C₁ E₁ h21 h22 hl0₁)
    (hashHead_ok C₂ E₂ h21₂ h22₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_
  have r3₂ := H₂.r3
  rw [hlen] at r3₂
  refine rel_seq (rel_ite (eval_zero H₁.r3 (by omega_arith)) (eval_zero r3₂ (by omega_arith)) (fun _ => rel_skip)
      (fun hb => hashLoop_rel hV C₁ C₂ h28 hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok C₁ h28 H₁) (hashBody_ok C₂ h28₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (tailHead_ok C₁ h22 G₁)
    (tailHead_ok C₂ h22₂ G₂) fun w₁ w₂ ⟨T₁, h25₁⟩ ⟨T₂, h25₂⟩ => ?_
  rw [hlen] at h25₂
  exact rel_ite (eval_zero h25₁ (by omega_arith)) (eval_zero h25₂ (by omega_arith)) (fun _ => rel_skip)
    fun _ => hashRest_rel hV C₁.lay C₁.rounds h28 T₁.env T₂.env (by rw [T₁.r24, T₂.r24, hlen]) (by rw [h25₁, h25₂])

end

end VG.Proof.AesOcb.PPC64LE
