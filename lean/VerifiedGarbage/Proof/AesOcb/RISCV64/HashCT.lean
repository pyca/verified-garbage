module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesOcb.RISCV64.HashChunk
import VerifiedGarbage.Proof.AesOcb.RISCV64.Hash
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.HashChunk
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Hash
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesOcb.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-OCB on RISC-V: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`, which each loads from its
slot in `W`. That address and the counts of blocks a chunk loads from `W`
(the blocks left, at `W + hlO`, and the chunk's, at `W + cnO`), which the
taint analysis takes as secret, are the same in both runs by the correctness
proofs (`HInv`, `FillInv`), which also pin the pointer `s4` and the index
`s6`: the blocks are split after each load (`chunkLd_ok`, `sumArgs_ok`).
Each chunk fills its buffer and adds it to the sum by code the taint
analysis checks, with the call between on the same arguments (`chunk_rel`);
both runs are at the same chunk at each iteration (`hashLoop_rel`); the
rest, if any, likewise (`hashRest_rel`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/HashCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Ocb (Block Cipher)
open VG.Proof.AesGcm.RISCV64 (frozen Keeps)

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
theorem Agree.perm {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} (h : Perm (V₂ .s2) (V₂ .s0) s) :
    Perm (V₁ .s2) (V₁ .s0) s := by
  rw [hV .s2 (by decide), hV .s0 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (hV : Agree V₁ V₂)
include hV

/-- The rest of the associated data, in two runs from the same `s4` and `s5`. -/
theorem hashRest_rel (L : Lay (V₁ .s2) (V₁ .s0)) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hs3 : V₁ .s3 = BitVec.ofNat 64 R) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h4 : σ₁.gpr .s4 = σ₂.gpr .s4) (h5 : σ₁.gpr .s5 = σ₂.gpr .s5) :
    RelCT isa (Eq2 σ₁ σ₂) hashRest TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.s4, .s5] (by agree_rv64 [h4, h5])
    ⟨_, by taint_decide⟩) [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .a3] (by decide +kernel) (by decide +kernel)
    (by decide) fun τ₁ τ₂ F₁ F₂ => ?_))
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

variable {D : Addr} {n R : Nat} {A : Addr} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte}
  {s₁ s₂ : State} (C₁ : HCtx (V₁ .s2) (V₁ .s0) D n R ciph₁ l₁ A a₁ s₁)
  (C₂ : HCtx (V₂ .s2) (V₂ .s0) D n R ciph₂ l₂ A a₂ s₂) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
  (hlen : a₂.length = a₁.length)
include C₁ C₂ hs3 hlen

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel {τ₁ τ₂ : State} {j : Nat} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ j)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ j) (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hs := C₁.short
  have L := C₁.lay
  have e0 := hV .s0 (by decide)
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have hl₂ := H₂.hl
  rw [hlen] at hl₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq ?_ (chunkHead_ok (k := a₁.length / 16 - j) L H₁.env.s0 H₁.env.perm.w
      (by omega_arith) H₁.hl)
    (chunkHead_ok (k := a₁.length / 16 - j) C₂.lay H₂.env.s0 H₂.env.perm.w (by omega_arith) hl₂)
    fun t₁ t₂ ⟨h5₁, g₁, k₁⟩ ⟨h5₂, g₂, k₂⟩ => ?_)
  · -- the number of blocks of the chunk, from those left
    refine rel_seq (rel_env H₁.env H₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
      (chunkLd_ok (k := a₁.length / 16 - j) L H₁.env.s0 H₁.env.perm.w (by omega_arith) H₁.hl)
      (chunkLd_ok (k := a₁.length / 16 - j) C₂.lay H₂.env.s0 H₂.env.perm.w (by omega_arith) hl₂)
      fun u₁ u₂ ⟨r1₁, r2₁, _, k₁⟩ ⟨r1₂, r2₂, _, k₂⟩ => ?_
    have hsp : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, H₁.env.sp, H₂.env.sp]
    refine rel_ite (eval_zero r2₁ (by omega_arith)) (eval_zero r2₂ (by omega_arith)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_taint [.t1] hsp (by agree_rv64 [r1₁, r1₂]) ⟨_, by taint_decide⟩
    · exact rel_taint [] hsp (by agree_rv64 []) ⟨_, by taint_decide⟩
  have E₁ := H₁.env.keep3 g₁ k₁
  have E₂ := H₂.env.keep3 g₂ k₂
  -- the counts stored
  refine rel_seq (rel_env E₁ E₂ hV [.s5] (by agree_rv64 [h5₁, h5₂]) ⟨_, by taint_decide⟩)
    (chunkMid_ok C₁ H₁ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₁ k₁ h5₁)
    (chunkMid_ok C₂ H₂ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₂ k₂ h5₂) fun w₁ w₂ F₁ F₂ => ?_
  -- the buffer filled
  refine rel_seq (rel_env F₁.env F₂.env hV [.a7, .s4, .s5, .s6]
      (by agree_rv64 [F₁.a7, F₂.a7, F₁.s4, F₂.s4, F₁.s5, F₂.s5, F₁.s6, F₂.s6, e0]) ⟨_, by taint_decide⟩)
    (fill_ok C₁ (by omega_arith) (by omega_arith) (by omega_arith) F₁)
    (fill_ok C₂ (by omega_arith) (by omega_arith) (by omega_arith) F₂)
    fun y₁ y₂ G₁ G₂ => ?_
  -- enciphered
  let c := min 8 (a₁.length / 16 - j)
  refine RelCT.assoc (rel_seq (F₁ := fun z => Env V₁ sp z ∧
      z.mem.readW (V₁ .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (F₂ := fun z => Env V₂ sp z ∧ z.mem.readW (V₂ .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (callBlocks_rel L hV Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct C₁.rounds hs3 G₁.env G₂.env [] (by agree_rv64 []) ⟨_, by taint_decide⟩
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₁.env.s0])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₂.env.s0, e0])
        (by rw [k.wr, e0]; exact G₂.env.perm.w) (by rw [k.mem, e0, G₂.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))
      (dstW L (hV.perm G₂.env.perm) (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames
      C₁.rounds hs3 G₁.env
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₁.env.s0])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₁.env, (bufCall_readW L P (by omega_arith) (d := cnO) (by decide)).trans G₁.cn⟩)
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (hV.lay L) Proof.Aes.RISCV64.encryptBlocks_correct
      encryptBlocks_noFrames C₁.rounds hs3₂ G₂.env
      (fun s g k => bufArgs_ok (hV.lay L) (by rw [g _ (by decide) (by decide) (by decide), G₂.env.s0])
        (by rw [k.wr]; exact G₂.env.perm.w) (by rw [k.mem, G₂.cn]))
      (dstW (hV.lay L) G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₂.env, (bufCall_readW (hV.lay L) P (by omega_arith) (d := cnO) (by decide)).trans G₂.cn⟩)
    fun z₁ z₂ ⟨Z₁, cn₁⟩ ⟨Z₂, cn₂⟩ => ?_)
  -- the buffer added to the sum
  refine rel_seq (rel_env Z₁ Z₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (sumArgs_ok L Z₁.s0 Z₁.perm.w cn₁) (sumArgs_ok (hV.lay L) Z₂.s0 Z₂.perm.w cn₂)
    fun x₁ x₂ ⟨a7₁, s5₁, g₁', k₁'⟩ ⟨a7₂, s5₂, g₂', k₂'⟩ => ?_
  have X₁ := Z₁.keep2 g₁' k₁'
  have X₂ := Z₂.keep2 g₂' k₂'
  refine rel_seqEnv X₁ X₂ (rel_env X₁ X₂ hV [.a7, .s5] (by agree_rv64 [a7₁, a7₂, s5₁, s5₂, e0])
    ⟨_, by taint_decide⟩) sumRegs (by decide +kernel) (by decide +kernel) (by decide) fun _ _ e₁ e₂ => ?_
  exact rel_env e₁ e₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel {τ₁ τ₂ : State} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ 0)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ 0) (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop hashChunk (.nonzero .t1)) TT := by
  have hs := C₁.short
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv V₁ sp ciph₁ l₁ A a₁ s₁ u₁ j ∧ HInv V₂ sp ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((chunk_rel hV C₁ C₂ hs3 hlen G₁ G₂ hj).wp
    (F₁ := fun u => HInv V₁ sp ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => HInv V₂ sp ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hashChunk_ok C₁ hs3 G₁ hj, hashChunk_ok C₂ hs3₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.t1 (by omega_arith)
  have t1₂ := F₂.t1
  rw [hlen] at t1₂
  have ev₂ := eval_nonzero t1₂ (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega_arith, j + min 8 (a₁.length / 16 - j), rfl,
    by omega_arith, F₁, F₂⟩

/-- `HASH`, in two runs, each with `A` in its slot of `W`. -/
theorem hash_rel (E₁ : Env V₁ sp s₁) (E₂ : Env V₂ sp s₂)
    (hA₁ : s₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.aadO) 64 = A)
    (hA₂ : s₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.aadO) 64 = A)
    (h10 : V₁ .s10 = BitVec.ofNat 64 a₁.length)
    (hl0₁ : Spec.Ocb.blockAtMem s₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₁ 0)
    (hl0₂ : Spec.Ocb.blockAtMem s₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) Impl.AesOcb.RISCV64.hash TT := by
  have hs := C₁.short
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have h10₂ : V₂ .s10 = BitVec.ofNat 64 a₂.length := by rw [← hV .s10 (by decide), h10, hlen]
  unfold Impl.AesOcb.RISCV64.hash
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (hashHead_ok C₁ E₁ hA₁ h10 hl0₁)
    (hashHead_ok C₂ E₂ hA₂ h10₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_
  have t1₂ := H₂.t1
  rw [hlen] at t1₂
  refine rel_seq (rel_ite (eval_zero H₁.t1 (by omega_arith)) (eval_zero t1₂ (by omega_arith)) (fun _ => rel_skip)
      (fun hb => hashLoop_rel hV C₁ C₂ hs3 hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok C₁ hs3 H₁) (hashBody_ok C₂ hs3₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (tailHead_ok C₁ h10 G₁)
    (tailHead_ok C₂ h10₂ G₂) fun w₁ w₂ ⟨T₁, h5₁⟩ ⟨T₂, h5₂⟩ => ?_
  rw [hlen] at h5₂
  exact rel_ite (eval_zero h5₁ (by omega_arith)) (eval_zero h5₂ (by omega_arith)) (fun _ => rel_skip)
    fun _ => hashRest_rel hV C₁.lay C₁.rounds hs3 T₁.env T₂.env (by rw [T₁.s4, T₂.s4, hlen]) (by rw [h5₁, h5₂])

end

end VG.Proof.AesOcb.RISCV64
