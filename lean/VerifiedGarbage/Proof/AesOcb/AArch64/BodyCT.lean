import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.AesOcb.AArch64.Body

/-!
# AES-OCB on AArch64: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the data's address and length (`x21`, `x28`), the number of whole
blocks (`x26`) and, for the rest, its address and length (`x23`, `x24`),
which are the same in both runs; what each piece keeps of them is read off
its instructions (`exec_keep`) or from its correctness proof. The calls have
the same arguments in both runs (`callBlocks_rel`).
-/

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
  exact rel_ite (eval_zero x24₁ (by omega)) (eval_zero x24₂ (by omega)) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
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
  exact rel_ite (eval_zero a₁ (by omega)) (eval_zero a₂ (by omega)) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
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
