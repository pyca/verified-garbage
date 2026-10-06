import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.AesOcb.AArch64.Hash

/-!
# AES-OCB on AArch64: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`. The first block loads `A`
and the length from `W` (which the taint analysis takes as secret, so no
later code uses them from there); the correctness proofs pin `x23` (the
position in the data), `x25` (the block's index) and `x26` (the blocks left)
to the same values in both runs. Each chunk fills its buffer and adds it to
the sum by code the taint analysis checks from those, with the call between
on the same arguments (`chunk_rel`); both runs are at the same chunk at each
iteration (`hashLoop_rel`); the rest, if any, likewise (`hashRest_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero eval_nonzero)

section
variable {K W D : Addr} {n R : Nat} {SP : Addr} {A : Addr}
  {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte} {s₁ s₂ : State}

/-- The blocks of the rest of the associated data, before its call. -/
theorem hashRestPre_ok (C : HCtx K W D n R ciph₁ l₁ A a₁ s₁) {t : State}
    (H : HInv K W D R n SP ciph₁ l₁ A a₁ s₁ t (a₁.length / 16)) (hr : 0 < a₁.length % 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (a₁.length % 16)) :
    WP isa (.seq (.seq (.block (xor16 .x20 240 ohO)) (padTo bufO)) (.block (xor16 .x19 ohO bufO))) t
      (Env K W D R n SP) := by
  have E := H.env
  have hs := C.short
  generalize hm : a₁.length / 16 = m at H
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x20) (a := 240) (d := ohO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  have hB := C.buf.slice (a := 16 * m) (k := a₁.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩))
  refine WP.mono (padTo_ok E₁.x19 E₁.perm.w hr (by omega) (by decide)
    (by rw [B₁.gpr _ (by decide), H.x23]) (by rw [B₁.gpr _ (by decide), h24]) hS hSD)
    fun t₂ ⟨_, _, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have E₂ := E₁.others g₂ sp₂ rd₂ wr₂
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .x19) (a := ohO) (d := bufO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  exact WP.of_runBlock ⟨t₃, run₃, E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr⟩

/-- The rest of the associated data, in two runs. -/
theorem hashRest_rel (v : BlocksImpl) (C₁ : HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State}
    (H₁ : HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ (a₁.length / 16))
    (H₂ : HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ (a₂.length / 16)) (hr : 0 < a₁.length % 16)
    (h24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (a₁.length % 16)) (h24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (a₂.length % 16)) :
    RelCT isa (Eq2 τ₁ τ₂) (hashRest (callees v)) TT := by
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seq (rel_env H₁.env H₂.env [.x23, .x24]
      (by agree_tac [H₁.x23, H₂.x23, h24₁, h24₂, hlen]) ⟨_, by taint_decide⟩)
    (hashRestPre_ok C₁ H₁ hr h24₁) (hashRestPre_ok C₂ H₂ (by rw [hlen]; exact hr) h24₂) fun u₁ u₂ E₁ E₂ => ?_))
  have L := C₁.lay
  refine rel_seq (callBlocks_rel v.encOk v.encCt L C₁.rounds E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (oneBlock_ok E₁.x19 bufO (by decide)) (oneBlock_ok E₂.x19 bufO (by decide))
      (dstW L E₁.perm (d := bufO) (n := 1) (by decide)) (dstW L E₂.perm (d := bufO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L E₁ C₁.rounds (oneBlock_ok E₁.x19 bufO (by decide))
      (dstW L E₁.perm (d := bufO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L E₂ C₁.rounds (oneBlock_ok E₂.x19 bufO (by decide))
      (dstW L E₂.perm (d := bufO) (n := 1) (by decide))) fun w₁ w₂ P₁ P₂ => ?_
  exact rel_env (E₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (E₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) []
    (by agree_tac []) ⟨_, by taint_decide⟩

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel (v : BlocksImpl) (C₁ : HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State} {j : Nat}
    (H₁ : HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ j) (H₂ : HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ j)
    (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) (hashChunk (callees v)) TT := by
  have hs := C₁.short
  have L := C₁.lay
  have x26₂ := H₂.x26
  rw [hlen] at x26₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq (rel_env H₁.env H₂.env [.x26] (by agree_tac [H₁.x26, x26₂]) ⟨_, by taint_decide⟩)
    (chunkHead_ok (L := a₁.length / 16 - j) (by omega) H₁.x26)
    (chunkHead_ok (L := a₁.length / 16 - j) (by omega) x26₂)
    fun t₁ t₂ ⟨h24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨h24₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  have H₁' := H₁.head g₁ m₁ sp₁ rd₁ wr₁
  have H₂' := H₂.head g₂ m₂ sp₂ rd₂ wr₂
  obtain ⟨u₁, run₁, F₁⟩ := bufStart_inv H₁' h24₁
  obtain ⟨u₂, run₂, F₂⟩ := bufStart_inv H₂' h24₂
  refine rel_seq (F₁ := fun t => FillInv K W D R n SP ciph₁ l₁ A a₁ s₁ j (min 8 (a₁.length / 16 - j)) t 0)
    (F₂ := fun t => FillInv K W D R n SP ciph₂ l₂ A a₂ s₂ j (min 8 (a₁.length / 16 - j)) t 0)
    (rel_env H₁'.env H₂'.env [.x24] (by agree_tac [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨u₁, run₁, F₁⟩) (WP.of_runBlock ⟨u₂, run₂, F₂⟩) fun u₁ u₂ F₁ F₂ => ?_
  have x26f := F₂.x26
  rw [hlen] at x26f
  refine rel_seq (rel_env F₁.env F₂.env [.x15, .x23, .x24, .x25, .x26, .x27]
      (by agree_tac [F₁.x15, F₂.x15, F₁.x23, F₂.x23, F₁.x24, F₂.x24, F₁.x25, F₂.x25, F₁.x26, x26f, F₁.x27, F₂.x27])
      ⟨_, by taint_decide⟩)
    (fill_ok C₁ (by omega) (by omega) (by omega) F₁) (fill_ok C₂ (by omega) (by omega) (by omega) F₂)
    fun w₁ w₂ G₁ G₂ => ?_
  have x26g := G₂.x26
  rw [hlen] at x26g
  refine rel_seq (callBlocks_rel v.encOk v.encCt L C₁.rounds G₁.env G₂.env [.x24] (by agree_tac [G₁.x24, G₂.x24])
      ⟨_, by taint_decide⟩ (bufArgs_ok G₁.env.x19 G₁.x24) (bufArgs_ok G₂.env.x19 G₂.x24)
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega))
      (dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₁.env C₁.rounds (bufArgs_ok G₁.env.x19 G₁.x24)
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₂.env C₁.rounds (bufArgs_ok G₂.env.x19 G₂.x24)
      (dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega))) fun y₁ y₂ P₁ P₂ => ?_
  have a₁ : y₁.gpr .x24 = w₁.gpr .x24 := P₁.saved _ (by decide) (by decide)
  have a₂ : y₂.gpr .x24 = w₂.gpr .x24 := P₂.saved _ (by decide) (by decide)
  have b₁ : y₁.gpr .x26 = w₁.gpr .x26 := P₁.saved _ (by decide) (by decide)
  have b₂ : y₂.gpr .x26 = w₂.gpr .x26 := P₂.saved _ (by decide) (by decide)
  exact rel_env (G₁.env.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (G₂.env.of_saved P₂.saved P₂.sp P₂.rd P₂.wr)
    [.x24, .x26] (by agree_tac [a₁, a₂, b₁, b₂, G₁.x24, G₂.x24, G₁.x26, x26g]) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel (v : BlocksImpl) (C₁ : HCtx K W D n R ciph₁ l₁ A a₁ s₁)
    (C₂ : HCtx K W D n R ciph₂ l₂ A a₂ s₂) (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State}
    (H₁ : HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ 0) (H₂ : HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ 0)
    (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop (hashChunk (callees v)) (.nonzero .x .x26)) TT := by
  have hs := C₁.short
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv K W D R n SP ciph₁ l₁ A a₁ s₁ u₁ j ∧ HInv K W D R n SP ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((chunk_rel v C₁ C₂ hlen G₁ G₂ hj).wp
    (F₁ := fun u => HInv K W D R n SP ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => HInv K W D R n SP ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hashChunk_ok v C₁ G₁ hj, hashChunk_ok v C₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.x26 (by omega)
  have ev₂ := eval_nonzero F₂.x26 (by rw [hlen]; omega)
  rw [hlen] at ev₂
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega, j + min 8 (a₁.length / 16 - j), rfl,
    by omega, F₁, F₂⟩

/-- `HASH`, in two runs. -/
theorem hash_rel (v : BlocksImpl) (C₁ : HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) (E₁ : Env K W D R n SP s₁) (E₂ : Env K W D R n SP s₂)
    (haad₁ : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (haad₂ : s₂.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen₁ : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₁.length)
    (halen₂ : s₂.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₂.length)
    (hl0₁ : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 l0O) = lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) (Impl.AesOcb.AArch64.hash (callees v)) TT := by
  have hs := C₁.short
  unfold Impl.AesOcb.AArch64.hash
  refine RelCT.assoc (rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (hashHead_ok C₁ E₁ haad₁ halen₁ hl0₁) (hashHead_ok C₂ E₂ haad₂ halen₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_)
  have x26₂ := H₂.x26
  rw [hlen] at x26₂
  refine rel_seq (rel_ite (eval_zero H₁.x26 (by omega)) (eval_zero x26₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial)
      (fun hb => hashLoop_rel v C₁ C₂ hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok v C₁ H₁) (hashBody_ok v C₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (tailHead_ok C₁ halen₁ G₁) (tailHead_ok C₂ halen₂ G₂) fun w₁ w₂ ⟨T₁, h24₁⟩ ⟨T₂, h24₂⟩ => ?_
  have h24₂' := h24₂
  rw [hlen] at h24₂'
  exact rel_ite (eval_zero h24₁ (by omega)) (eval_zero h24₂' (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    (fun hb => hashRest_rel v C₁ C₂ hlen T₁ T₂ (by have := of_decide_eq_false hb; omega) h24₁ h24₂)

end

end VG.Proof.AesOcb.AArch64
