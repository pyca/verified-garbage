module

public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.AArch64.InitCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Args
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.AesOcb.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.AesOcb.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ocb.State
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesOcb.AArch64.InitCT
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Body
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Spec.Ocb
meta import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.AesOcb.AArch64.Hash
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Hash

/-! ### `AesOcb.AArch64.OpenCT`, which only this module used -/

section

/-! ### `AesOcb.AArch64.SealCT`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.HashCT`, which only this module used -/

section

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

@[expose] public section

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
  have hB := C.buf.slice (a := 16 * m) (k := a₁.length % 16) (by omega_arith)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩))
  refine WP.mono (padTo_ok E₁.x19 E₁.perm.w hr (by omega_arith) (by decide)
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
    (chunkHead_ok (L := a₁.length / 16 - j) (by omega_arith) H₁.x26)
    (chunkHead_ok (L := a₁.length / 16 - j) (by omega_arith) x26₂)
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
    (fill_ok C₁ (by omega_arith) (by omega_arith) (by omega_arith) F₁) (fill_ok C₂ (by omega_arith) (by omega_arith) (by omega_arith) F₂)
    fun w₁ w₂ G₁ G₂ => ?_
  have x26g := G₂.x26
  rw [hlen] at x26g
  refine rel_seq (callBlocks_rel v.encOk v.encCt L C₁.rounds G₁.env G₂.env [.x24] (by agree_tac [G₁.x24, G₂.x24])
      ⟨_, by taint_decide⟩ (bufArgs_ok G₁.env.x19 G₁.x24) (bufArgs_ok G₂.env.x19 G₂.x24)
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))
      (dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₁.env C₁.rounds (bufArgs_ok G₁.env.x19 G₁.x24)
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₂.env C₁.rounds (bufArgs_ok G₂.env.x19 G₂.x24)
      (dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))) fun y₁ y₂ P₁ P₂ => ?_
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
  have ev₁ := eval_nonzero F₁.x26 (by omega_arith)
  have ev₂ := eval_nonzero F₂.x26 (by rw [hlen]; omega_arith)
  rw [hlen] at ev₂
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega_arith, j + min 8 (a₁.length / 16 - j), rfl,
    by omega_arith, F₁, F₂⟩

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
  refine rel_seq (rel_ite (eval_zero H₁.x26 (by omega_arith)) (eval_zero x26₂ (by omega_arith))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial)
      (fun hb => hashLoop_rel v C₁ C₂ hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok v C₁ H₁) (hashBody_ok v C₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (tailHead_ok C₁ halen₁ G₁) (tailHead_ok C₂ halen₂ G₂) fun w₁ w₂ ⟨T₁, h24₁⟩ ⟨T₂, h24₂⟩ => ?_
  have h24₂' := h24₂
  rw [hlen] at h24₂'
  exact rel_ite (eval_zero h24₁ (by omega_arith)) (eval_zero h24₂' (by omega_arith))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    (fun hb => hashRest_rel v C₁ C₂ hlen T₁ T₂ (by have := of_decide_eq_false hb; omega_arith) h24₁ h24₂)

end

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.BodyCT`, which this module and modules that import it used -/

section

/-!
# AES-OCB on AArch64: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the data's address and length (`x21`, `x28`), the number of whole
blocks (`x26`) and, for the rest, its address and length (`x23`, `x24`),
which are the same in both runs; what each piece keeps of them is read off
its instructions (`exec_keep`) or from its correctness proof. The calls have
the same arguments in both runs (`callBlocks_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero lsr_ofNat)

section
variable {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) {d : Nat}
    (hd : d = tagO ∨ d = t2O) : RelCT isa (Eq2 σ₁ σ₂) (tag (callees v) d) TT := by
  have mid : ∀ {τ₁ τ₂ : State}, Env K W D R n SP τ₁ → Env K W D R n SP τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) (.seq (callBlocks (callees v).enc (oneBlock tmpO)) (.block (copy16 tmpO d ++
        xor16 .x19 sumO d))) TT := fun {τ₁ τ₂} F₁ F₂ => by
    refine rel_seq (callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
        (oneBlock_ok F₁.x19 tmpO (by decide)) (oneBlock_ok F₂.x19 tmpO (by decide))
        (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
      (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (oneBlock_ok F₁.x19 tmpO (by decide))
        (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
      (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (oneBlock_ok F₂.x19 tmpO (by decide))
        (dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ P₁ P₂ => ?_
    rcases hd with rfl | rfl <;>
      exact rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) []
        (by agree_tac []) ⟨_, by taint_decide⟩
  unfold tag
  exact rel_seqE (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (fun _ _ h => E₁.exec h (by decide +kernel) (by decide +kernel))
    (fun _ _ h => E₂.exec h (by decide +kernel) (by decide +kernel)) fun _ _ F₁ F₂ => mid F₁ F₂

/-- The rest of the data (`r` bytes at `P`), in two runs. -/
theorem rest_rel (v : BlocksImpl) (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂)
    {P : Addr} {r : Nat} (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 r) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 r) :
    RelCT isa (Eq2 σ₁ σ₂) (rest (callees v) enc) TT := by
  have keep : ∀ {σ : State}, Env K W D R n SP σ → σ.gpr .x23 = P → σ.gpr .x24 = BitVec.ofNat 64 r →
      ∀ t s', Exec isa (.block (xor16 .x20 240 ofsO ++ copy16 ofsO tmpO)) σ t s' →
        Env K W D R n SP s' ∧ s'.gpr .x23 = P ∧ s'.gpr .x24 = BitVec.ofNat 64 r := fun E h23 h24 _ _ h => by
    obtain ⟨g, sp, rd, wr⟩ := exec_keep [.x19, .x20, .x21, .x22, .x28, .x23, .x24] (by decide +kernel)
      (by decide +kernel) h
    exact ⟨E.keep (fun q hq => g q (List.mem_append_left _ hq)) sp rd wr,
      by rw [g _ (by simp), h23], by rw [g _ (by simp), h24]⟩
  unfold rest
  refine rel_seqE (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (keep E₁ h23₁ h24₁) (keep E₂ h23₂ h24₂)
    fun τ₁ τ₂ ⟨F₁, a₁, b₁⟩ ⟨F₂, a₂, b₂⟩ => ?_
  refine rel_seq (callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (oneBlock_ok F₁.x19 tmpO (by decide)) (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (oneBlock_ok F₁.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ P₁ P₂ => ?_
  have c23₁ : u₁.gpr .x23 = τ₁.gpr .x23 := P₁.saved _ (by decide) (by decide)
  have c23₂ : u₂.gpr .x23 = τ₂.gpr .x23 := P₂.saved _ (by decide) (by decide)
  have c24₁ : u₁.gpr .x24 = τ₁.gpr .x24 := P₁.saved _ (by decide) (by decide)
  have c24₂ : u₂.gpr .x24 = τ₂.gpr .x24 := P₂.saved _ (by decide) (by decide)
  cases enc <;>
    exact rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) [.x23, .x24]
      (by agree_tac [c23₁, c23₂, c24₁, c24₂, a₁, a₂, b₁, b₂]) ⟨_, by taint_decide⟩

/-- The rest of the data, if there is any, in two runs. -/
theorem restIte_rel (v : BlocksImpl) (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) (hn : n < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10,
      .sub .x .x9 .x28 .x24, .add .x .x23 .x21 .x9]) (.ite (.zero .x .x24) (.block []) (rest (callees v) enc))) TT := by
  obtain ⟨t₁, run₁, x23₁, x24₁, _, g₁, sp₁, rd₁, wr₁⟩ := bodyTail_ok E₁ hn
  obtain ⟨t₂, run₂, x23₂, x24₂, _, g₂, sp₂, rd₂, wr₂⟩ := bodyTail_ok E₂ hn
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨t₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨t₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_ite (eval_zero x24₁ (by omega_using [])) (eval_zero x24₂ (by omega_using [])) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    fun _ => rest_rel L hR v enc (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) x23₁ x23₂ x24₁ x24₂

/-- The whole blocks (`m` of them, in `x26`), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true) {pre post : List Instr} {pm qm : CkMode}
    (hc₁ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre)) h).isSome = true)
    (hk₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre) : Prog isa).allInstrs
        (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28, .x26])) = true)
    (hn₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre) : Prog isa).noCalls = true)
    (hc₂ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block (copy16 o0O ofsO ++ ([Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] : List Instr))) (passFast qm post)) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) {m : Nat}
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 m) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 m)
    (hD₁ : DBuf K W σ₁ D (16 * m)) (hD₂ : DBuf K W σ₂ D (16 * m)) :
    RelCT isa (Eq2 σ₁ σ₂) (whole b pre post pm qm) TT := by
  have keep : ∀ {σ : State}, Env K W D R n SP σ → σ.gpr .x26 = BitVec.ofNat 64 m → DBuf K W σ D (16 * m) →
      ∀ t s', Exec isa (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre)) σ t s' →
        Env K W D R n SP s' ∧ s'.gpr .x26 = BitVec.ofNat 64 m ∧ DBuf K W s' D (16 * m) := fun E h26 hD _ _ h => by
    obtain ⟨g, sp, rd, wr⟩ := exec_keep _ hk₁ hn₁ h
    exact ⟨E.keep (fun q hq => g q (List.mem_append_left _ hq)) sp rd wr,
      by rw [g _ (by simp), h26], hD.of_eq rd wr⟩
  unfold whole
  refine RelCT.assoc (rel_seqE (rel_env E₁ E₂ [.x26] (by agree_tac [h26₁, h26₂]) hc₁) (keep E₁ h26₁ hD₁)
    (keep E₂ h26₂ hD₂) fun τ₁ τ₂ ⟨F₁, a₁, d₁⟩ ⟨F₂, a₂, d₂⟩ => ?_)
  refine rel_seq (callBlocks_rel ok ct L hR F₁ F₂ [.x26] (by agree_tac [a₁, a₂]) ⟨_, by taint_decide⟩
      (dataArgs_ok F₁.x21 a₁) (dataArgs_ok F₂.x21 a₂) (dstD d₁) (dstD d₂))
    (callBlocks_ok ok nf L F₁ hR (dataArgs_ok F₁.x21 a₁) (dstD d₁))
    (callBlocks_ok ok nf L F₂ hR (dataArgs_ok F₂.x21 a₂) (dstD d₂)) fun u₁ u₂ P₁ P₂ => ?_
  have c₁ : u₁.gpr .x26 = τ₁.gpr .x26 := P₁.saved _ (by decide) (by decide)
  have c₂ : u₂.gpr .x26 = τ₂.gpr .x26 := P₂.saved _ (by decide) (by decide)
  exact rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) [.x26]
    (by agree_tac [c₁, c₂, a₁, a₂]) hc₂

/-- The whole blocks, if there are any, in two runs. -/
theorem wholeIte_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true) {pre post : List Instr} {pm qm : CkMode}
    (hc₁ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre)) h).isSome = true)
    (hk₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre) : Prog isa).allInstrs
        (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28, .x26])) = true)
    (hn₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (passFast pm pre) : Prog isa).noCalls = true)
    (hc₂ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block (copy16 o0O ofsO ++ ([Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] : List Instr))) (passFast qm post)) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) (hD₁ : DBuf K W σ₁ D n)
    (hD₂ : DBuf K W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block [.lsr .x .x26 .x28 4]) (.ite (.zero .x .x26) (.block [])
      (whole b pre post pm qm))) TT := by
  have hn := hD₁.lt
  have lsr : ∀ {σ : State}, Env K W D R n SP σ →
      WP isa (.block [.lsr .x .x26 .x28 4]) σ fun t => Env K W D R n SP t ∧ t.gpr .x26 = BitVec.ofNat 64 (n / 16) ∧
        t.rd = σ.rd ∧ t.wr = σ.wr := fun {σ} E =>
    WP.of_runBlock ⟨σ.write .x .x26 (σ.gpr .x28 >>> 4), by orun [], E.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl,
      by simp [gpr_write, E.x28, lsr_ofNat _ _ hn], rfl, rfl⟩
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (lsr E₁) (lsr E₂)
    fun τ₁ τ₂ ⟨F₁, a₁, r₁, w₁⟩ ⟨F₂, a₂, r₂, w₂⟩ => ?_
  exact rel_ite (eval_zero a₁ (by omega_using [hn])) (eval_zero a₂ (by omega_using [hn])) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    fun _ => whole_rel L hR ok ct nf hc₁ hk₁ hn₁ hc₂ F₁ F₂ a₁ a₂ ((hD₁.take' (Nat.mul_div_le n 16)).of_eq r₁ w₁)
      ((hD₂.take' (Nat.mul_div_le n 16)).of_eq r₂ w₂)

/-- `body` for `seal`, in two runs. -/
theorem bodySeal_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂)
    (hD₁ : DBuf K W σ₁ D n) (hD₂ : DBuf K W σ₂ D n) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ofsO) = O₁) (ho0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₁.mem K) 0)
    (hofs₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ofsO) = O₂) (ho0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₂.mem K) 0) :
    RelCT isa (Eq2 σ₁ σ₂) (body (callees v) true) TT := by
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel L hR v.encOk v.encCt v.encNoFrames ⟨_, by taint_decide⟩
      (by decide +kernel) (by decide +kernel) ⟨_, by taint_decide⟩ E₁ E₂ hD₁ hD₂)
    (wholeIte_ok (O0 := O₁) (l := ctxLstar σ₁.mem K)
      (ckF1 := ckOf fun i => blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
      v.encOk v.encNoFrames hcall_enc sealPre_ok xorOfs_ok rfl rfl L E₁ hR hD₁ hofs₁ ho0₁ hck₁ hl0₁
      (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok (O0 := O₂) (l := ctxLstar σ₂.mem K)
      (ckF1 := ckOf fun i => blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
      v.encOk v.encNoFrames hcall_enc sealPre_ok xorOfs_ok rfl rfl L E₂ hR hD₂ hofs₂ ho0₂ hck₂ hl0₂
      (fun _ => rfl) rfl (fun _ => rfl)) fun t₁ t₂ P₁ P₂ => ?_)
  exact restIte_rel L hR v true P₁.env P₂.env hD₁.lt

/-- `body` for `open`, in two runs. -/
theorem bodyOpen_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂)
    (hD₁ : DBuf K W σ₁ D n) (hD₂ : DBuf K W σ₂ D n) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ofsO) = O₁) (ho0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₁.mem K) 0)
    (hofs₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ofsO) = O₂) (ho0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₂.mem K) 0) :
    RelCT isa (Eq2 σ₁ σ₂) (body (callees v) false) TT := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel L hR v.decOk v.decCt v.decNoFrames ⟨_, by taint_decide⟩
      (by decide +kernel) (by decide +kernel) ⟨_, by taint_decide⟩ E₁ E₂ hD₁ hD₂)
    (wholeIte_ok (O0 := O₁) (l := ctxLstar σ₁.mem K) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => decG (bytesAt σ₁.mem K (16 * (R + 1)))
        (blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₁ (ctxLstar σ₁.mem K) (i + 1)) ^^^
          offAt O₁ (ctxLstar σ₁.mem K) (i + 1))
      v.decOk v.decNoFrames hcall_dec xorOfs_ok openPost_ok rfl rfl L E₁ hR hD₁ hofs₁ ho0₁ hck₁ hl0₁
      (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok (O0 := O₂) (l := ctxLstar σ₂.mem K) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => decG (bytesAt σ₂.mem K (16 * (R + 1)))
        (blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₂ (ctxLstar σ₂.mem K) (i + 1)) ^^^
          offAt O₂ (ctxLstar σ₂.mem K) (i + 1))
      v.decOk v.decNoFrames hcall_dec xorOfs_ok openPost_ok rfl rfl L E₂ hR hD₂ hofs₂ ho0₂ hck₂ hl0₂
      (fun _ => rfl) rfl (fun _ => rfl)) fun t₁ t₂ P₁ P₂ => ?_)
  exact restIte_rel L hR v false P₁.env P₂.env hD₁.lt

end

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.NonceCT`, which only this module used -/

section

/-!
# AES-OCB on AArch64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. `nonceBlock` loads the
nonce's address and length from `W`: its first block is split there, and the
rest runs from them (`nonceBlock_rel`); then the call (`callBlocks_rel`) and
`offset0`, whose shifts by `bottom` are masks, not branches (`nonce_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq)

theorem nonceBlock_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {N : Addr} {nl : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    RelCT isa (Eq2 σ₁ σ₂) nonceBlock TT := by
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, -, -, sp₁, rd₁, wr₁⟩ := nonceHead_ok E₁.x19 E₁.perm.w hN₁ hnl₁
  obtain ⟨s₂, run₂, x12₂, x13₂, g₂, -, -, sp₂, rd₂, wr₂⟩ := nonceHead_ok E₂.x19 E₂.perm.w hN₂ hnl₂
  unfold nonceBlock
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.keep (fun r hr => g₁ r (envRegs_ne hr) (envRegs_ne hr) (envRegs_ne hr)) sp₁ rd₁ wr₁)
    (E₂.keep (fun r hr => g₂ r (envRegs_ne hr) (envRegs_ne hr) (envRegs_ne hr)) sp₂ rd₂ wr₂) [.x12, .x13]
    (by agree_tac [x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

theorem nonce_rel (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {σ₁ σ₂ : State}
    (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB₁ : Buf W σ₁ N nl) (hB₂ : Buf W σ₂ N nl) :
    RelCT isa (Eq2 σ₁ σ₂) (nonce (callees v)) TT := by
  unfold nonce
  refine rel_seq (nonceBlock_rel E₁ E₂ hN₁ hN₂ hnl₁ hnl₂)
    (nonceBlock_ok L E₁.x19 E₁.perm.w hN₁ hnl₁ htl₁ h1 h15 ht hB₁)
    (nonceBlock_ok L E₂.x19 E₂.perm.w hN₂ hnl₂ htl₂ h1 h15 ht hB₂) fun τ₁ τ₂ P₁ P₂ => ?_
  have F₁ : Env K W D R n SP τ₁ := E₁.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₂ : Env K W D R n SP τ₂ := E₂.others P₂.gpr P₂.sp P₂.rd P₂.wr
  refine rel_seq (callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (oneBlock_ok F₁.x19 tmpO (by decide)) (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (oneBlock_ok F₁.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ Q₁ Q₂ => ?_
  exact rel_env (F₁.of_saved Q₁.saved Q₁.sp Q₁.rd Q₁.wr) (F₂.of_saved Q₂.saved Q₂.sp Q₂.rd Q₂.wr) []
    (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load, and the rest runs from `x9`, which holds
`work` (public) in both runs (`entry_rel`). Then `nonce_rel`, `hash_rel`
(`pre_rel`), `bodySeal_rel`, `tag_rel`, the copy of the tag, whose first
block loads the tag's address from the stack and is split there
(`tagOut_rel`), and `restore`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of in_off RelCT.block_split)

/-- The entry of `seal` and `open`, in two runs. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hargs₁ : Covers [⟨σ₁.sp, 24⟩] (σ₁.rd ++ σ₁.wr)) (hargs₂ : Covers [⟨σ₂.sp, 24⟩] (σ₂.rd ++ σ₂.wr))
    (qsp : σ₁.sp = σ₂.sp) (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨_, run₁, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₁) (i := 2) (by decide) (in_off hargs₁ (by decide) (by decide))
  obtain ⟨_, run₂, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₂) (i := 2) (by decide) (in_off hargs₂ (by decide) (by decide))
  simp only [Nat.reduceMul] at run₁ run₂
  rw [entry]
  simp only [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨_, run₁, rfl⟩) (WP.of_runBlock ⟨_, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_)
  subst h₁ h₂
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by simp only [sp_write]; exact qsp) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; simp [gpr_write, hW₁, hW₂]
  · simp only [gpr_write, h9, ite_false]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

/-- `entry`, `nonce` and `hash`, in two runs with the same public arguments. -/
theorem pre_rel (v : BlocksImpl) {σ₁ σ₂ : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (A₁ : Args σ₁ K W N A D R nl al n tl T) (A₂ : Args σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h0₁ : σ₁.gpr .x0 = K) (h1₁ : σ₁.gpr .x1 = BitVec.ofNat 64 R) (h2₁ : σ₁.gpr .x2 = N)
    (h3₁ : σ₁.gpr .x3 = BitVec.ofNat 64 nl) (h4₁ : σ₁.gpr .x4 = A) (h5₁ : σ₁.gpr .x5 = BitVec.ofNat 64 al)
    (h6₁ : σ₁.gpr .x6 = D) (h7₁ : σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h0₂ : σ₂.gpr .x0 = K) (h1₂ : σ₂.gpr .x1 = BitVec.ofNat 64 R) (h2₂ : σ₂.gpr .x2 = N)
    (h3₂ : σ₂.gpr .x3 = BitVec.ofNat 64 nl) (h4₂ : σ₂.gpr .x4 = A) (h5₂ : σ₂.gpr .x5 = BitVec.ofNat 64 al)
    (h6₂ : σ₂.gpr .x6 = D) (h7₂ : σ₂.gpr .x7 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (callees v)) (hash (callees v)))) TT := by
  have L := A₁.lay
  refine rel_seq (entry_rel hW₁ hW₂ A₁.args A₂.args qsp
      (by agree_tac [h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂]))
    (entry_ok L A₁.perm hW₁ htl₁ A₁.args A₁.argsW h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ h6₁ h7₁)
    (entry_ok L A₂.perm hW₂ htl₂ A₂.args A₂.argsW h0₂ h1₂ h2₂ h3₂ h4₂ h5₂ h6₂ h7₂) fun s₁ s₂ P₁ P₂ => ?_
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega_using [this]
  refine rel_seq (nonce_rel v L P₁.env E₂ A₁.rounds P₁.slots.nonce P₂.slots.nonce P₁.slots.nlen P₂.slots.nlen
      P₁.slots.tl P₂.slots.tl A₁.n1 A₁.n15 ht (A₁.nonce.of_eq P₁.rd P₁.wr) (A₂.nonce.of_eq P₂.rd P₂.wr))
    (nonce_ok v L P₁.env A₁.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl A₁.n1 A₁.n15 ht
      (A₁.nonce.of_eq P₁.rd P₁.wr) A₁.data.k)
    (nonce_ok v L E₂ A₁.rounds P₂.slots.nonce P₂.slots.nlen P₂.slots.tl A₁.n1 A₁.n15 ht
      (A₂.nonce.of_eq P₂.rd P₂.wr) A₁.data.k) fun t₁ t₂ Q₁ Q₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w (nonceR_mut Q₁.frame) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w (nonceR_mut Q₂.frame) P₂.slots
  exact hash_rel v (hctx_of A₁ P₁ Q₁) (hctx_of A₂ P₂ Q₂) (by rw [length_bytesAt, length_bytesAt]) Q₁.env Q₂.env
    S₁.aad S₂.aad (by rw [length_bytesAt]; exact S₁.alen) (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [Q₁.keep (by decide) (by decide), P₁.l0]) (by rw [Q₂.keep (by decide) (by decide), P₂.l0])

/-- `Args` in two runs with the same public arguments, with the values of the
first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : Args σ₂ (σ₂.gpr .x0) (stackArg σ₂ 2) (σ₂.gpr .x2) (σ₂.gpr .x4) (σ₂.gpr .x6) (σ₂.gpr .x1).toNat
      (σ₂.gpr .x3).toNat (σ₂.gpr .x5).toNat (σ₂.gpr .x7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `pre_rel` and `pre_wp'` in two runs with the same public arguments, then
`k`. -/
theorem pre_relk (v : BlocksImpl) {σ₁ σ₂ : State}
    (A₁ : Args σ₁ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (hq : onePub σ₁ σ₂) {k : Prog isa}
    (hk : ∀ τ₁ τ₂, Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₁ τ₁ →
      Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  refine RelCT.assoc_in (RelCT.assoc (rel_seq (pre_rel v A₁ A₂ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
      (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5) q6.symm
      (o' q7) qsp)
    (pre_wp' v A₁ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _))
    (pre_wp' v A₂ (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5)
      q6.symm (o' q7)) hk))

/-- Two runs of `front; tail` are two runs of `front`'s pieces, then `tail`. -/
theorem rel_front {P Q : State → State → Prop} {e n h b t tail : Prog isa}
    (hr : RelCT isa P (.seq e (.seq n (.seq h (.seq b (.seq t tail))))) Q) :
    RelCT isa P (.seq (.seq e (.seq n (.seq h (.seq b t)))) tail) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq f₁ r₁ => cases f₁ with | seq a₁ f₁ => cases f₁ with | seq b₁ f₁ =>
  cases f₁ with | seq c₁ f₁ => cases f₁ with | seq d₁ g₁ =>
  cases e₂ with | seq f₂ r₂ => cases f₂ with | seq a₂ f₂ => cases f₂ with | seq b₂ f₂ =>
  cases f₂ with | seq c₂ f₂ => cases f₂ with | seq d₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq g₁ r₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq g₂ r₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `tagOut` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem tagOut_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) tagOut TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := tagOutHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := tagOutHead_ok E₂ htl₂ hT₂ ha₂
  unfold tagOut
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The state after `front`, in a run with the arguments: the address of the
tag on the stack, where the state may read it. -/
theorem front_tag {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W N A D R nl al n tl T) (hT : stackArg s 0 = T) {s₃ s₄ s₅ : State} {d : Nat} (hd : d + 16 ≤ 160)
    (P : Pre K W D R n N A nl al tl s s₃) {out : List Byte} {ofs ck : Spec.Ocb.Block}
    {SP SP' : Addr} (B : BodyPost K W D R n SP' out ofs ck s₃ s₄) (T₅ : TagPost K W D R n SP d s₄ s₅)
    (hsp : SP = s.sp) :
    stackArg s₅ 0 = T ∧ InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
  have sp₅ : s₅.sp = s.sp := T₅.env.sp.trans hsp
  refine ⟨?_, ?_⟩
  · rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact args_kept Ar.argsW Ar.argsD (front_frame hd P.frame B.frame T₅.frame) (i := 0) (by decide)
  · rw [T₅.rd, B.rd, P.rd, T₅.wr, B.wr, P.wr, sp₅]
    exact in_off Ar.args (by decide) (by decide)

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := sealArgs_of h₁
  have A₂ := args₂_of hq (sealArgs_of h₂)
  have qsp := hq.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «seal» front
  refine rel_front (pre_relk v A₁ A₂ hq fun τ₁ τ₂ P₁ P₂ => ?_)
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (bodySeal_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame]))
    (bodySeal_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, ctxLstar_W L P₁.frame]))
    (bodySeal_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L A₁.rounds v B₁.env B₂.env (.inl rfl)) (tag_ok v L B₁.env A₁.rounds (.inl rfl))
    (tag_ok v L B₂.env A₁.rounds (.inl rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((bodyR_mut B₁.frame).trans (tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((bodyR_mut B₂.frame).trans (tagR_mut (by decide) T₂.frame)) P₂.slots
  obtain ⟨t₁, a₁⟩ := front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (tagOut_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (tagOut_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by
      rw [T₁.wr, B₁.wr, P₁.wr, h₁.2.1]; exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₁.tag.w)
    (tagOut_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by
      rw [T₂.wr, B₂.wr, P₂.wr, h₂.2.1, ← qT, hq.2.2.2.2.2.2.2.2.2 1 (by decide)]
      exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₂.tag.w)
    fun y₁ y₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  exact rel_env (T₁.env.others g₁ sp₁ rd₁ wr₁) (T₂.env.others g₂ sp₂ rd₂ wr₂) [] (by agree_tac [])
    ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.Open`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.CmpMask`, which this module and modules that import it used -/

section

/-!
# AES-OCB on AArch64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.AArch64 (read_one succ_ofNat bytesAt_succ in_of_covers eval_zero eval_nonzero)

/-! ## `cmp` -/

theorem zext8 (b : BitVec (8 * 1)) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.setWidth 64 (b : Byte) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem setWidth_xor_eq_zero (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64 = 0#64) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 63` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit {x : BitVec 64} (h : x.toNat < 256) :
    (x - BitVec.ofNat 64 1) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 1 % 2 ^ 64 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]

/-- The registers `cmp` writes. -/
abbrev cmpRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

abbrev cmpBody : List Instr :=
  [.ldrb .x9 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x9 .x9 .x10, .logic .orr .x .x13 .x13 .x9,
    Impl.AesGcm.AArch64.ptr .x11 .x11 1, Impl.AesGcm.AArch64.ptr .x12 .x12 1, .subImm .x .x24 .x24 1]

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {A B : Addr} (ha : s.gpr .x11 = A) (hb : s.gpr .x12 = B)
    (ra : InRegions (s.rd ++ s.wr) A 1) (rb : InRegions (s.rd ++ s.wr) B 1) :
    ∃ s', runBlock isa cmpBody s = some s' ∧ s'.mem = s.mem ∧
      s'.gpr .x13 = s.gpr .x13 ||| ((s.mem A).setWidth 64 ^^^ (s.mem B).setWidth 64) ∧
      s'.gpr .x11 = A + BitVec.ofNat 64 1 ∧ s'.gpr .x12 = B + BitVec.ofNat 64 1 ∧
      s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ cmpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [ha, hb, ra, rb], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_write, read_one, zext8, ha, hb]
  · simp [gpr_write, ha]
  · simp [gpr_write, hb]
  · simp [gpr_write]
  · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`'s first block: the tag length, and the two tags' addresses. -/
theorem cmpHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {tl : Nat}
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s₁, runBlock isa
        [Impl.AesGcm.AArch64.imm .x13 0, Impl.AesGcm.AArch64.mov .x11 .x19, Impl.AesGcm.AArch64.ptr .x12 .x19 t2O,
          ld .x24 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x13 = 0#64 ∧ s₁.gpr .x11 = W + BitVec.ofNat 64 0 ∧ s₁.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 0 ∧
      s₁.gpr .x24 = BitVec.ofNat 64 (tl - 0) ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ cmpRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₀ := E.perm.wR (show 248 + 8 ≤ 2560 by decide)
  simp only [tlO] at htl
  refine ⟨_, by orun [E.x19, r₀, htl], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19, t2O]
  · simp [gpr_write, htl]
  · rfl
  · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ∉ cmpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, x13₁, x11₁, x12₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := cmpHead_ok E htl
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR (by omega_arith)
  -- The loop: the OR of the XORs of the first `j` bytes in `x13`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .nonzero .x .x24)
    (Q := fun u => (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .x11 = W + BitVec.ofNat 64 j ∧
      u.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 j ∧ u.gpr .x24 = BitVec.ofNat 64 (tl - j) ∧
      (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega_arith, x11₁, x12₁, x24₁, by rw [x13₁]; decide, by rw [x13₁]; simp [bytesAt], m₁, g₁, sp₁, rd₁,
      wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, x11, x12, x24, lt, iff, mem, g, sp, rd, wr⟩
    obtain ⟨u', run', mem', x13', x11', x12', x24', g', sp', rd', wr'⟩ := cmpStep_ok u x11 x12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega_arith))
      (by rw [rd, wr]; exact hR (by simp only [t2O]; omega_arith))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at x13'
    have lt' : (u'.gpr .x13).toNat < 256 := by
      rw [x13', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor _ _)
    have iff' : u'.gpr .x13 = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [x13', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero, bytesAt_succ, bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have x24'' : u'.gpr .x24 = BitVec.ofNat 64 (tl - (j + 1)) := by
      rw [x24', x24, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
    have ev := eval_nonzero (r := .x24) (a := tl - (j + 1)) x24'' (by omega_arith)
    have gg : ∀ r, r ∉ cmpRegs → u'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
    by_cases he : j + 1 = tl
    · left
      exact ⟨by rw [ev]; simp [he], lt', by rw [iff', he], by rw [mem', mem], gg, by rw [sp', sp],
        by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by rw [ev]; simp; omega_arith, tl - (j + 1), by omega_arith, j + 1, rfl, by omega_arith,
        by rw [x11', Offset.add_add], by rw [x12', Offset.add_add], x24'', lt', iff', by rw [mem', mem], gg,
        by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, sp, rd, wr⟩ := hu
    have h19 : u.gpr .x19 = W := by rw [g _ (by decide), E.x19]
    have w₀ : InRegions u.wr W 8 := by rw [wr]; simpa using E.perm.wW (d := 0) (n := 8) (by decide)
    refine WP.of_runBlock ⟨_, by orun [h19, w₀], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, gpr_write, ite_true, mem, tagO, BitVec.add_zero]
      rw [okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]
      · simp only [mt iff.mp he, he, ↓reduceIte]
    · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
      simp only [gpr_write, h₅, ite_false]
      exact g r (by simp [cmpRegs, h₁, h₂, h₃, h₄, h₅, h₆])
    all_goals simp only [sp, rd, wr, sp_write, rd_write, wr_write, mem_write]

/-! ## `mask` -/

theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 b)) &&& BitVec.setWidth 32 (0#64 - (if c then 1#64 else 0#64))))) =
      if c then (b : Byte) else 0 := by
  cases c
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0#64 - 1#64 : BitVec 64) = BitVec.allOnes 64 by decide]
    simp [BitVec.getLsbD_setWidth, show i < 32 by omega_arith, show i < 64 by omega_arith, hi]
    intro _
    rw [BitVec.getElem_eq_testBit_toNat, show (255#8).toNat = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]

/-- The registers `mask` writes. -/
abbrev maskRegs : List Reg := [.x9, .x10, .x23, .x24]

abbrev maskBody : List Instr :=
  [.ldrb .x9 .x23 0, .logic .and .w .x9 .x9 .x10, .strb .x9 .x23 0, Impl.AesGcm.AArch64.ptr .x23 .x23 1,
    .subImm .x .x24 .x24 1]

theorem maskStep_ok (s : State) {P : Addr} {c : Bool} (h23 : s.gpr .x23 = P)
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64))
    (rq : InRegions (s.rd ++ s.wr) P 1) (wq : InRegions s.wr P 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW P ((if c then s.mem P else 0 : Byte)) ∧
      s'.gpr .x23 = P + BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [h23, rq, wq, write1], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h10, h23, read_one, mask_byte]
  · simp [gpr_write, h23]
  · simp [gpr_write]
  · simp [gpr_write, h₁, h₂, h₃]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem maskVector_ok (s : State) {P : Addr} {c : Bool} (h23 : s.gpr .x23 = P)
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64))
    (rq : InRegions (s.rd ++ s.wr) P 16) (wq : InRegions s.wr P 16) :
    ∃ s', runBlock isa [.vop (.dup .d2 .v0 .x10), .ldrq .v1 .x23 0,
        .vop (.logic .and .v1 .v1 .v0), .strq .v1 .x23 0,
        Impl.AesGcm.AArch64.ptr .x23 .x23 16, .subImm .x .x24 .x24 16] s = some s' ∧
      s'.mem = writeBytes s.mem P (if c then bytesAt s.mem P 16 else zeros 16) ∧
      s'.gpr .x23 = P + BitVec.ofNat 64 16 ∧ s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hm (v : BitVec 128) : v &&& ofVDwords (0#64 - (if c then 1#64 else 0#64))
      (0#64 - (if c then 1#64 else 0#64)) = if c then v else 0 := by
    cases c
    · simp [ofVDwords]
    · change v &&& BitVec.allOnes 128 = v
      exact BitVec.and_allOnes
  refine ⟨_, by orun [h23, rq, wq, VOp.eval, v_setV, gpr_setV, mem_setV, rd_setV, wr_setV,
      sp_setV], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_setV, mem_setV, v_setV, ↓reduceIte, reduceCtorEq, h10, h23,
      BitVec.add_zero, hm]
    rw [write_eq_writeBytes]
    congr 1
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · decide
    · apply List.map_congr_left
      intro j hj
      exact Mem.extractLsb'_read _ _ (List.mem_range.mp hj)
  · simp [gpr_write, gpr_setV, h23]
  · simp [gpr_write, gpr_setV]
  · simp [gpr_write, gpr_setV, h₂, h₃]
  all_goals rfl

/-- A vector if one remains, otherwise a single tail byte. The branch depends only on length. -/
theorem maskSmall_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (hj : j < n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n - j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa maskSmall s fun t => ∃ b, 0 < b ∧ j + b ≤ n ∧
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j + b) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, x9, g, m, sp, rd, wr⟩ : ∃ s₁,
      runBlock isa [.lsr .x .x9 .x24 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 ((n-j) / 16) ∧
      (∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, h24, BitVec.setWidth_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Proof.Ocb.toNat_ofNat_of_lt (by omega_arith),
        Proof.Ocb.toNat_ofNat_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
    · simp [gpr_write, hr]
    all_goals rfl
  unfold maskSmall
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide ((n-j)/16 = 0)) (eval_zero x9 (by omega_arith)) (fun hb => ?_) (fun hb => ?_)
  · obtain ⟨t, run, mem, xp, xc, gg, ss, rr, ww⟩ := maskStep_ok s₁ (P := D + BitVec.ofNat 64 j) (c := c)
      (by rw [g _ (by decide)]; exact h23) (by rw [g _ (by decide)]; exact h10)
      (by rw [rd, wr]; exact in_of_covers hD.rd hj hn)
      (by rw [wr]; exact in_of_covers hD.wr hj hn)
    refine WP.of_runBlock ⟨t, run, 1, by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ss.trans sp, rr.trans rd, ww.trans wr⟩
    · rw [mem, m, Proof.Ocb.writeW8_eq]; cases c <;> simp [bytesAt, zeros]
    · rw [xp, Offset.add_add]
    · rw [xc, g _ (by decide), h24, Offset.ofNat_sub_ofNat (by omega_arith)]
      congr 1
    · exact fun r h₁ h₂ h₃ => (gg r h₁ h₂ h₃).trans (g r h₁)
  · have hb : 16 ≤ n-j := by have := of_decide_eq_false hb; omega_arith
    obtain ⟨t, run, mem, xp, xc, gg, ss, rr, ww⟩ := maskVector_ok s₁ (P := D + BitVec.ofNat 64 j) (c := c)
      (by rw [g _ (by decide)]; exact h23) (by rw [g _ (by decide)]; exact h10)
      (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_off hD.rd (by omega_arith) hn)
      (by rw [wr]; exact Proof.AesGcm.AArch64.in_off hD.wr (by omega_arith) hn)
    refine WP.of_runBlock ⟨t, run, 16, by omega_arith, by omega_arith, by rw [mem, m], ?_, ?_, ?_,
      ss.trans sp, rr.trans rd, ww.trans wr⟩
    · rw [xp, Offset.add_add]
    · rw [xc, g _ (by decide), h24, Offset.ofNat_sub_ofNat (by omega_arith)]
      congr 1
    · exact fun r h₁ h₂ h₃ => (gg r h₁ h₂ h₃).trans (g r h₁)


theorem maskVectors_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (k : Nat) (hk : j + 16*k ≤ n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n-j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa (maskVectors k) s fun t =>
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) (16*k) else zeros (16*k)) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j+16*k) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n-(j+16*k)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  induction k generalizing s j with
  | zero =>
    refine WP.block_nil ⟨?_, by simpa using h23, by simpa using h24, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  | succ k ih =>
    have hn := hD.lt
    obtain ⟨u,run,mem,xp,xc,g,sp,rd,wr⟩ := maskVector_ok s h23 h10
      (Proof.AesGcm.AArch64.in_off hD.rd (by omega_arith) hn)
      (Proof.AesGcm.AArch64.in_off hD.wr (by omega_arith) hn)
    refine WP.seq (WP.of_runBlock ⟨u,run,?_⟩)
    have xp' : u.gpr .x23 = D + BitVec.ofNat 64 (j+16) := by rw [xp,Offset.add_add]
    have xc' : u.gpr .x24 = BitVec.ofNat 64 (n-(j+16)) := by
      rw [xc,h24,Offset.ofNat_sub_ofNat (by omega_arith),Nat.sub_sub]
    refine WP.mono (ih (hD.of_eq rd wr) (by omega_arith) xp' xc'
      (by rw [g _ (by decide) (by decide) (by decide),h10])) fun t ⟨mt,xt,ct,gt,st,rt,wt⟩ => ?_
    refine ⟨?_,by simpa only [show j+16+16*k = j+16*(k+1) by omega_arith] using xt,
      by simpa only [show j+16+16*k = j+16*(k+1) by omega_arith] using ct,
      fun r a b c => (gt r a b c).trans (g r a b c),st.trans sp,rt.trans rd,wt.trans wr⟩
    have hq : bytesAt u.mem (D+BitVec.ofNat 64 (j+16)) (16*k) =
        bytesAt s.mem (D+BitVec.ofNat 64 (j+16)) (16*k) := by
      apply List.map_congr_left
      intro i hi
      have hi : i < 16*k := List.mem_range.mp hi
      rw [mem, show D+BitVec.ofNat 64 (j+16) = (D+BitVec.ofNat 64 j)+16#64 from (Offset.add_add D j 16).symm,
        Offset.add_add]
      simp only [writeBytes,length_mask,Mem.sub_ofNat_toNat (D+BitVec.ofNat 64 j) (show 16+i < 2^64 by omega_arith),
        show ¬16+i < 16 by omega_arith,ite_false]
    rw [mt,hq,mem]
    have app := writeBytes_append s.mem (D+BitVec.ofNat 64 j)
      (if c then bytesAt s.mem (D+BitVec.ofNat 64 j) 16 else zeros 16)
      (if c then bytesAt s.mem (D+BitVec.ofNat 64 (j+16)) (16*k) else zeros (16*k))
      (by rw [length_mask,length_mask]; omega_arith)
    rw [length_mask,Offset.add_add] at app
    rw [app]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, zeros, List.replicate_append_replicate,
        show 16*(k+1) = 16+16*k by omega_arith]
    · simp [show 16*(k+1) = 16+16*k by omega_arith,Proof.AesGcm.AArch64.bytesAt_add,Offset.add_add]

/-- Mask four complete vectors, one vector, or one byte depending only on length. -/
theorem maskChunk_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (hj : j < n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n - j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa maskChunk s fun t => ∃ b, 0 < b ∧ j + b ≤ n ∧
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j + b) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let u := s.write .x .x9 (s.gpr .x24 >>> 6)
  have hu : runBlock isa [.lsr .x .x9 .x24 6] s = some u := by orun []
  have hg (r : Reg) (hr : r ≠ .x9) : u.gpr r = s.gpr r := by simp [u,gpr_write,hr]
  have h9 : u.gpr .x9 = BitVec.ofNat 64 ((n-j)/64) := by
    simp [u,gpr_write,h24,Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n-j < 2^64 by have := hD.lt; omega_arith)]
  unfold maskChunk
  refine WP.seq (WP.of_runBlock ⟨u,hu,?_⟩)
  refine WP.ite _ (eval_zero h9 (by have := hD.lt; omega_arith)) (fun hz => ?_) (fun hn => ?_)
  · refine WP.mono (maskSmall_ok (s := u) (hD.of_eq rfl rfl) hj ((hg _ (by decide)).trans h23)
      ((hg _ (by decide)).trans h24) ((hg _ (by decide)).trans h10)) ?_
    rintro t ⟨b,hb,hjb,mem,xp,xc,g,sp,rd,wr⟩
    exact ⟨b,hb,hjb,mem,xp,xc,fun r a b c => (g r a b c).trans (hg r a),sp,rd,wr⟩
  · have hn : 64 ≤ n-j := by have := of_decide_eq_false hn; omega_arith
    refine WP.mono (maskVectors_ok (s := u) (hD.of_eq rfl rfl) 4 (by omega_arith) ((hg _ (by decide)).trans h23)
      ((hg _ (by decide)).trans h24) ((hg _ (by decide)).trans h10)) ?_
    rintro t ⟨mem,xp,xc,g,sp,rd,wr⟩
    exact ⟨64,by decide,by omega_arith,mem,xp,xc,fun r a b c => (g r a b c).trans (hg r a),sp,rd,wr⟩

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) (hD : DBuf K W s D n)
    {c : Bool} (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s fun t => (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have r₃ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (d := 0) (n := 8) (by decide)
  simp only [tagO, BitVec.add_zero] at hok
  have hok' : s.mem.readW W 64 = if c then 1#64 else 0#64 := by simpa using hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, x23₁, x24₁, x10₁, g₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x28, ld .x9 .x19 tagO,
        Impl.AesGcm.AArch64.imm .x10 0, .sub .x .x10 .x10 .x9] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .x23 = D ∧ s₁.gpr .x24 = BitVec.ofNat 64 n ∧
      s₁.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₃, hok'], ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x28]
    · simp [gpr_write, hok']
    · simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
      simp [gpr_write, h₁, h₂, h₃, h₄]
    all_goals rfl
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_zero x24₁ hn) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨g₁, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .nonzero .x .x24)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .x23 = D + BitVec.ofNat 64 j ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - j) ∧ t.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [x23₁]; simp, x24₁, x10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      g₁, sp₁, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, x23, x24, x10, mem, g, sp, rd, wr⟩
  refine WP.mono (maskChunk_ok (hD.of_eq rd wr) hj x23 x24 x10) ?_
  rintro t' ⟨b, hb, hjb, mem', x23', x24', g', sp', rd', wr'⟩
  have hq : bytesAt t.mem (D + BitVec.ofNat 64 j) b = bytesAt s.mem (D + BitVec.ofNat 64 j) b := by
    apply List.map_congr_left
    intro i hi
    have hi : i < b := List.mem_range.mp hi
    rw [Offset.add_add, mem]
    simp only [writeBytes, length_mask, Mem.sub_ofNat_toNat D (show j + i < 2 ^ 64 by omega_arith),
      show ¬j + i < j by omega_arith, ite_false]
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + b) else zeros (j + b)) := by
    rw [mem', hq, mem]
    have append := writeBytes_append s.mem D (if c then bytesAt s.mem D j else zeros j)
      (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b)
      (by rw [length_mask, length_mask]; omega_arith)
    rw [length_mask] at append
    rw [append]
    cases c <;> simp [zeros, Proof.AesGcm.AArch64.bytesAt_add]
  have x24'' : t'.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) := by
    exact x24'
  have ev := eval_nonzero (r := .x24) (a := n - (j + b)) x24'' (by omega_arith)
  have gg : ∀ r, r ∉ maskRegs → t'.gpr r = s.gpr r := fun r hr => by
    simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g' r hr.1 hr.2.2.1 hr.2.2.2, g r (by simp [maskRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  by_cases he : j + b = n
  · left
    exact ⟨by rw [ev]; simp [he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, n - (j + b), by omega_arith, j + b, rfl, by omega_arith,
      x23', x24'', by rw [g' _ (by decide) (by decide) (by decide), x10], hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the copy of the received tag from `tag`, whose
address is on the stack, to `W` (`recv`), its comparison with the computed
tag (`cmp`), the mask of the data (`mask`), the result and `restore`
(`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- `recv`: the `tl` bytes of the tag at `T` copied to `W`. -/
theorem recv_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : stackArg s 0 = T) (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (hTr : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa recv s fun t => t.mem = writeBytes s.mem W (bytesAt s.mem T tl) ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := recvHead_ok E htl hT ha
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (Proof.AesGcm.AArch64.copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega_using [h1])
    ⟨by omega_using [h16], by rw [rd₁, wr₁]; exact hTr, by
      rw [wr₁]
      exact fun a m ⟨r, hr, hc⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [h16, hc]⟩,
      hTW.sub_right (Region.sub_prefix (by omega_using [h16]))⟩)
    fun t ⟨m, _, _, g, sp, rd, wr⟩ => ⟨by rw [m, m₁], fun r hr => by rw [g r hr, g₁ r hr], by rw [sp, sp₁],
      by rw [rd, rd₁], by rw [wr, wr₁]⟩

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W) (hT : stackArg s 0 = T)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («open» (callees v)) s fun s' => GprAbi s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  have hn := Ar.data.lt
  unfold «open» front
  refine WP.seq (pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_)
  obtain hD₃ : DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := ctxCiph_W L P₃.frame Ar.rounds
  obtain i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := ctxInv_W L P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := ctxLstar_W L P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := bytesAt_W Ar.data.w hn P₃.frame
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok v L B.env Ar.rounds (.inr rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  obtain S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  obtain Ff := front_frame (by decide) P₃.frame B.frame T₅.frame
  have sp₅ : s₅.sp = s.sp := T₅.env.sp
  -- The received tag, to `W`.
  obtain hT₅ : stackArg s₅ 0 = T := by
    rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact args_kept Ar.argsW Ar.argsD Ff (i := 0) (by decide)
  obtain ha₅ : InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
    rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr, sp₅]
    exact Proof.AesGcm.AArch64.in_off Ar.args (by decide) (by decide)
  refine WP.seq (WP.mono (recv_ok T₅.env Ar.t1 Ar.t16 S₅.tl hT₅ ha₅
    (by rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr]; exact Ar.tag.rd) Ar.tag.w)
    fun s₅' ⟨mr, gr, spr, rdr, wrr⟩ => ?_)
  obtain E₅' := T₅.env.others gr spr rdr wrr
  obtain Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain Fr' : Frame (mutR W D n) s₅.mem s₅'.mem := Fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := Ar.t16; omega_using [this])⟩
  obtain S₅' := Slots.of_mut L Ar.data.w Fr' S₅
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₅' Ar.t1 Ar.t16 S₅'.tl) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := E₅'.others g₆ sp₆ rd₆ wr₆
  obtain F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hD₆ : DBuf K W s₆ D n :=
    hD₃.of_eq (rd₆.trans (rdr.trans (T₅.rd.trans B.rd))) (wr₆.trans (wrr.trans (T₅.wr.trans B.wr)))
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ hD₆ (c := c)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨g₇, sp₇, rd₇, wr₇, m₇⟩ => ?_)
  obtain E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  obtain F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain F₃₇ : Frame (mutR W D n) s₃.mem s₇.mem :=
    (((F₄.trans F₅).trans Fr').trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide))).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutD fun _ h => h)
  -- The result, and `restore`.
  obtain ok₇ : s₇.mem.readW W 64 = if c then 1#64 else 0#64 := by
    obtain e : s₆.mem.readW W 64 = if c then 1#64 else 0#64 := by
      have := Mem.readW_writeW_self64 s₅'.mem (W + BitVec.ofNat 64 tagO)
        (if bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64)
      rw [← m₆] at this
      simp only [tagO, BitVec.add_zero] at this
      rw [this]; simp only [c, decide_eq_true_eq]
    rw [F₇.readW (r := ⟨W, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide), e]
  obtain r₀ : InRegions (s₇.rd ++ s₇.wr) W 8 := by simpa using E₇.perm.wR (d := 0) (n := 8) (by decide)
  obtain ⟨s₈, run₈, x0₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .x0 .x19 tagO] s₇ = some s₈ ∧
      s₈.gpr .x0 = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ∉ [Reg.x0] → s₈.gpr r = s₇.gpr r) ∧
      s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.x19, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · rfl
    · simp only [List.mem_singleton] at h
      simp [gpr_write, h]
    all_goals rfl
  obtain E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  obtain sv₈ : Spill.Saved W s.gpr saved s₈.mem := by
    rw [m₈]; exact saved_mut L Ar.data.w P₃.saved F₃₇
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  refine WP.mono (restore_wp' E₈ sv₈) fun s₉ Rs => ⟨restore_abi Rs E₈.sp, ?_⟩
  -- The plaintext and the comparison.
  obtain x0₉ : s₉.gpr .x0 = if c then 1#64 else 0#64 := by rw [Rs.other _ (by decide), x0₈]
  have hout := B.out
  rw [c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [c₃, i₃, l₃, d₃] at hck
  have hTn := Ar.tag.lt
  obtain recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
    rw [mr, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) (by omega_using [hTn]), length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]
    exact Proof.Cmac.bytesAt_frame Ff (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Ar.tag.w
      · exact Ar.td) (by omega_using [hTn])
  obtain t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame Fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega_using [this])
        (by have := Ar.t16; unfold t2O; omega_using [this])).symm) (by omega_using [hTn])
  have tagv := T₅.val
  rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
  obtain d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
    obtain d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega_using [hn]),
        Proof.Cmac.bytesAt_frame Fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_using [this]))) (by omega_using [hn]),
        Proof.Cmac.bytesAt_frame T₅.frame (tag_data Ar.data.w (by decide)) (by omega_using [hn])]
    rw [Rs.mem, m₈, m₇, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
  rw [x0₉, d₉, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  obtain hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openAArch64.pre s) :
    WP isa («open» (callees v)) s fun s' => GprAbi s s' ∧ openAArch64.post s s' :=
  open_wp' v (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the tag at
`W + t2O`; then the copy of the received tag to `W`, whose first block loads
the tag's address from the stack and is split there (`recv_rel`); then
`cmp`, which loads the tag length from `W`: its first block is split there,
and the comparison runs from it (`cmp_rel`); `mask` and the result read the
comparison's result only as data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)

/-- `cmp`, in two runs. -/
theorem cmp_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {tl : Nat} (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) : RelCT isa (Eq2 σ₁ σ₂) cmp TT := by
  obtain ⟨s₁, run₁, -, x11₁, x12₁, x24₁, -, g₁, sp₁, rd₁, wr₁⟩ := cmpHead_ok E₁ htl₁
  obtain ⟨s₂, run₂, -, x11₂, x12₂, x24₂, -, g₂, sp₂, rd₂, wr₂⟩ := cmpHead_ok E₂ htl₂
  have ne : ∀ r ∈ envRegs, r ∉ cmpRegs := by decide
  unfold cmp
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.keep (fun r hr => g₁ r (ne r hr)) sp₁ rd₁ wr₁) (E₂.keep (fun r hr => g₂ r (ne r hr)) sp₂ rd₂ wr₂)
    [.x11, .x12, .x24] (by agree_tac [x11₁, x11₂, x12₁, x12₂, x24₁, x24₂]) ⟨_, by taint_decide⟩

/-- `recv` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem recv_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) recv TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := recvHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := recvHead_ok E₂ htl₂ hT₂ ha₂
  unfold recv
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The received tag's copy to `W` keeps the slots. -/
theorem recv_slots {K W D : Addr} {n : Nat} (L : Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {tl : Nat}
    (h16 : tl ≤ 16) {m : Mem} {xs : List Byte} (hx : xs.length = tl) {N A : Addr} {nl al : Nat}
    (S : Slots W N A nl al tl m) : Slots W N A nl al tl (writeBytes m W xs) :=
  Slots.of_mut L hDW ((writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_using [h16])⟩) S

theorem open_ct (v : BlocksImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := openArgs_of h₁
  have A₂ := args₂_of hq.1 (openArgs_of h₂)
  have qsp := hq.1.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.1.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «open» front
  refine rel_front (pre_relk v A₁ A₂ hq.1 fun τ₁ τ₂ P₁ P₂ => ?_)
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (bodyOpen_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame]))
    (bodyOpen_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, ctxLstar_W L P₁.frame]))
    (bodyOpen_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L A₁.rounds v B₁.env B₂.env (.inr rfl)) (tag_ok v L B₁.env A₁.rounds (.inr rfl))
    (tag_ok v L B₂.env A₁.rounds (.inr rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((bodyR_mut B₁.frame).trans (tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((bodyR_mut B₂.frame).trans (tagR_mut (by decide) T₂.frame)) P₂.slots
  obtain ⟨t₁, a₁⟩ := front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (recv_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (recv_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by rw [T₁.rd, B₁.rd, P₁.rd, T₁.wr, B₁.wr, P₁.wr]; exact A₁.tag.rd)
      A₁.tag.w)
    (recv_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by rw [T₂.rd, B₂.rd, P₂.rd, T₂.wr, B₂.wr, P₂.wr]; exact A₂.tag.rd)
      A₂.tag.w)
    fun y₁ y₂ ⟨m₁, g₁, sp₁, rd₁, wr₁⟩ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have Y₁ := T₁.env.others g₁ sp₁ rd₁ wr₁
  have Y₂ := T₂.env.others g₂ sp₂ rd₂ wr₂
  have Sy₁ := recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₁.mem (stackArg σ₁ 0) _) S₁
  have Sy₂ := recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₂.mem (stackArg σ₁ 0) _) S₂
  rw [← m₁] at Sy₁
  rw [← m₂] at Sy₂
  refine rel_seq (cmp_rel Y₁ Y₂ Sy₁.tl Sy₂.tl) (cmp_ok Y₁ A₁.t1 A₁.t16 Sy₁.tl)
    (cmp_ok Y₂ A₁.t1 A₁.t16 Sy₂.tl) fun z₁ z₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ := Y₁.others g₁ sp₁ rd₁ wr₁
  have F₂ := Y₂.others g₂ sp₂ rd₂ wr₂
  refine rel_seqEnv F₁ F₂ (rel_env F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · intro z₁ z₂ G₁ G₂
    exact rel_env G₁ G₂ [] (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.Verified`, which only this module used -/

section

/-!
# AES-OCB on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`), a state satisfying each
precondition, and the shared contracts of `Spec/Ocb/Contract.lean` with the
working space as a last argument (`Proof/AesOcb/Scratch.lean`), with no
stack: the calls keep the return address in `x30`, which each function saves
in its working space. `Frame.lean` allocates the working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-! ## v8–v15 -/

theorem seal_keepsV (v : BlocksImpl) : («seal» (callees v)).allInstrs keepsV = true := by
  simp only [«seal», front, tagOut, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, passFast, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_keepsV (v : BlocksImpl) : («open» (callees v)).allInstrs keepsV = true := by
  simp only [«open», front, recv, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, passFast, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_keepsV (v : BlocksImpl) : (init (callees v)).allInstrs keepsV = true := by
  simp only [init, callees, Code.allInstrs, v.encKeepsV, v.expandKeepsV, Bool.true_and, Bool.and_true]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : BlocksImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

theorem init_correct (v : BlocksImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem seal_verified (v : BlocksImpl) :
    Verified AArch64.target («seal» (callees v)) (Proof.AesOcb.sealScratchContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealAArch64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem init_verified (v : BlocksImpl) :
    Verified AArch64.target (init (callees v)) (Proof.AesOcb.initScratchContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, initAArch64, AArch64.abi, AArch64.argRegs] [initSat] using initSat)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified AArch64.target («open» (callees v)) (Proof.AesOcb.openScratchContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`x3`): its frame holds the 2560 bytes
(`Verified.stackScratch`). The working space of `seal` and `open` is their
third stack argument, after `tag` and `tag_len`, so their frame of 2592
bytes holds a copy of those two, the address of the working space and the
working space, at the next 16-byte boundary (`Verified.stackArgScratch`).
The code itself uses no stack: its calls keep the return address in `x30`.
`open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init (callees v)))
      (Spec.Ocb.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre AArch64.abi.ptrBits) (post := Spec.Ocb.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide)
    (Proof.AesOcb.initPostOut_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    (Proof.AesOcb.sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre AArch64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ocb.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.AesOcb.openPre_local _)
    (Proof.AesOcb.openPost_local _)
    (Proof.AesOcb.openPostOut_local _) openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.AArch64
