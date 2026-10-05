import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
import VerifiedGarbage.Proof.AesOcb.X86_64.TagCT

/-!
# AES-OCB on x86-64: `HASH` is constant time

Untrusted: everything here is checked by Lean. Each chunk fills its buffer
and adds it to the sum by code that passes the taint analysis from the
public slots, the number of blocks left (at `W + alenO`) and the position
in the associated data (`rbx`, `rbp`); the call between has the same
arguments in both runs (`callBlocks_rel`), and so does the rest's. Both runs
are at the same chunk at each iteration (`chunk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne)

section
variable {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}

/-- A run of `HASH` keeps the public arguments. -/
theorem HInv.one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} {j : Nat} (H : HInv K W SP D n ciph l A a s₀ t j) :
    One K W SP R N A D nl n tl t :=
  ⟨H.env, Slots.of_mut C.lay C.dw (hashR_mut H.frame) o.sl, H.wr.trans o.wr⟩

theorem FillInv.one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} {j c i : Nat} (F : FillInv K W SP D n ciph l A a s₀ j c t i) :
    One K W SP R N A D nl n tl t :=
  ⟨F.env, Slots.of_mut C.lay C.dw (hashR_mut F.frame) o.sl, F.wr.trans o.wr⟩

/-- The first block and the chunks, if any. -/
theorem hashHI_ok (v : BlocksImpl) (C : HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) (.ite .e (.block []) (.loop (hashChunk (callees v)) .ne))) s₀
      fun t => HInv K W SP D n ciph l A a s₀ t (a.length / 16) := by
  refine WP.seq (WP.mono (hashHead_ok C E haad halen) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.ite (decide (a.length / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · exact (of_decide_eq_true hb) ▸ H₀
  · exact hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))

/-- The length of the rest. -/
theorem tailHead_ok {t : State} (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) t fun t₁ =>
      HInv K W SP D n ciph l A a s₀ t₁ (a.length / 16) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧
        t₁.zf = some (decide (a.length % 16 = 0)) := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 112) 8 := H.env.perm.wR (by decide)
  have rest := H.rest
  simp only [tmpO] at rest
  obtain ⟨t₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧ t₁.zf = some (decide (a.length % 16 = 0)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [H.env.r15, r₁, rest], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [zf_arithFlags, gpr_setReg, ite_true,
        Proof.AesCcm.X86_64.and_self_beq (show a.length % 16 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  exact WP.of_runBlock ⟨t₁, run₁,
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest] }, r12₁, zf₁⟩

/-- The rest of the associated data, before its call, keeps the public arguments. -/
theorem hashRestPre_one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16))
    (hr : 0 < a.length % 16) (h12 : t.gpr .r12 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (.seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO)))) t
      (One K W SP R N A D nl n tl) := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  have o₀ := H.one C o
  generalize hm : a.length / 16 = m at H
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ohO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₁.rd B₁.wr
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok E₁ hr (by omega) (by decide) (by rw [B₁.gpr _ (by decide), H.rbx])
    (by rw [B₁.gpr _ (by decide), h12]) hS hSD) fun t₂ ⟨fr₂, _, g₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ohO) (d := bufO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, run₃, o₀.step L C.dw E₃ (by rw [B₃.wr, wr₂, B₁.wr])
    (((B₁.frame.sub fun r hr => ?_).trans (fr₂.sub fun r hr => ?_)).trans (B₃.frame.sub fun r hr => ?_))⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩

end

/-- One chunk, at the same position in both runs. -/
theorem chunk_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : One K W SP R N A D nl n tl s₀₁) (o₂ : One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64) (k j : Nat) :
    RelCT isa (fun s₁ s₂ => k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (hashChunk (callees v)) fun s₁ s₂ => isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
          HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) ∧
        (isa.eval .ne s₁ = some true → ∃ m < k, ∃ j', m = a₁.length / 16 - j' ∧ j' < a₁.length / 16 ∧
          HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j' ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j') := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  obtain ⟨M, hMd⟩ : ∃ M, M = a₁.length / 16 := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = min 8 (M - j) := ⟨_, rfl⟩
  rw [← hMd]
  rw [← hMd] at hM
  by_cases hkj : k = M - j ∧ j < M
  swap
  · exact RelCT.of_false fun s₁ s₂ h => hkj ⟨h.1, h.2.1⟩
  obtain ⟨hk, hjM⟩ := hkj
  have pre : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, HCtx K W SP D n R ciph l A a s₀ →
      a.length / 16 = M → j < M → HInv K W SP D n ciph l A a s₀ s j →
      WP isa (.seq (.block [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
        (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne)))) s
        (FillInv K W SP D n ciph l A a s₀ j c · c) := fun {ciph l a s₀ s} C hm hj H => by
    have hc : min 8 (a.length / 16 - j) = c := by rw [hm, hcd]
    refine wp_seq_assoc (WP.seq (WP.mono (chunkHead_ok C H (by omega)) fun t ⟨H', h12⟩ => ?_))
    rw [hc] at h12
    exact chunkFill_ok C H' (by omega) (by omega) (by omega) h12
  have bX : ∀ s₁ s₂, (k = M - j ∧ j < M ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) → Both K W SP R N A D nl n tl [.rbx, .rbp] [248] s₁ s₂ :=
    fun s₁ s₂ ⟨_, _, H₁, H₂⟩ => by
      have O₁ := H₁.one C₁ o₁
      have O₂ := H₂.one C₂ o₂
      refine ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun x hx => ?_, fun d hd => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [H₁.rbx, H₂.rbx]
        · rw [H₁.rbp, H₂.rbp]
      · simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, H₁.alen, H₂.alen, hM, hMd]⟩
  have X := (rel_taintC [.rbx, .rbp] [248] hDW hn bX
    (c := .seq (.block [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
      (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne))))
    ⟨_, by taint_decide⟩).wp
    (F₁ := (FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c · c)) (F₂ := (FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c · c))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨pre C₁ hMd.symm hj H₁, pre C₂ hM hj H₂⟩
  have hc8 : c ≤ 8 := by omega
  have call : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, HCtx K W SP D n R ciph l A a s₀ →
      One K W SP R N A D nl n tl s₀ → FillInv K W SP D n ciph l A a s₀ j c s c →
      WP isa (callBlocks (callees v).enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) s fun s' =>
        One K W SP R N A D nl n tl s' ∧ s'.gpr .r12 = BitVec.ofNat 64 c := fun {ciph l a s₀ s} C o F => by
    have O := F.one C o
    exact WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L O.env C.rounds O.sl.rounds
      (bufArgs_ok F.env.r15 F.r12) (dstW L F.env.perm (d := 384) (n := c) (by omega))) fun s' Q => by
      refine ⟨O.step L hDW (O.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), F.r12]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, sub_wC (by decide) (by omega)⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [O.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have B := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] []
    (args := [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 384) (k := c)
    (P := fun s₁ s₂ => True ∧ FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c s₁ c ∧
      FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c s₂ c) fun s₁ s₂ h =>
      ⟨Both.of (h.2.1.one C₁ o₁) (h.2.2.one C₂ o₂), bufArgs_ok h.2.1.env.r15 h.2.1.r12,
        bufArgs_ok h.2.2.env.r15 h.2.2.r12, dstW L h.2.1.env.perm (d := 384) (n := c) (by omega),
        dstW L h.2.2.env.perm (d := 384) (n := c) (by omega)⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    fun s₁ s₂ h => ⟨call C₁ o₁ h.2.1, call C₂ o₂ h.2.2⟩
  have Y := rel_taintC [.r12] [] hDW hn (fun s₁ s₂ (h : True ∧ (One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 64 c) ∧ (One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r12 = BitVec.ofNat 64 c)) =>
    (⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; rw [h.2.1.2, h.2.2.2], fun _ h => (nomatch h)⟩ :
      Both K W SP R N A D nl n tl [.r12] [] s₁ s₂))
    (c := .seq hashSum (.block [ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))
    ⟨_, by taint_decide⟩
  have T : RelCT isa (fun s₁ s₂ => k = M - j ∧ j < M ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) (hashChunk (callees v)) fun _ _ => True := by
    unfold hashChunk; exact Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq X (RelCT.seq B Y))
  refine (T.wp (F₁ := fun (t : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (j + c) ∧
      t.zf = some (decide (M - (j + c) = 0)))
    (F₂ := fun (t : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (j + c) ∧ t.zf = some (decide (M - (j + c) = 0)))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨H₁, z₁⟩, ⟨H₂, z₂⟩⟩ => ?_
  · have := hashChunk_ok v C₁ H₁ (by omega)
    rw [← hMd, ← hcd] at this
    exact this
  · have := hashChunk_ok v C₂ H₂ (by omega)
    rw [hM, ← hcd] at this
    exact this
  · rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun h => ?_, fun h => ?_⟩
    · have he : j + c = M := by simp at h; omega
      rw [hM, ← he]; exact ⟨H₁, H₂⟩
    · have he : ¬ M - (j + c) = 0 := by simpa using h
      exact ⟨M - (j + c), by omega, j + c, rfl, by omega, H₁, H₂⟩

/-- The call on the block at `W + bufO` keeps the public arguments. -/
theorem callBuf_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State}
    (o : One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (callees v).enc (oneBlock bufO)) s (One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 bufO (by decide)) (dstW L o.env.perm (d := bufO) (n := 1) (by decide))) fun s' Q => by
    refine o.step L hDW (o.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `HASH` in two runs, from the starts `s₀₁` and `s₀₂` of the same length of associated data. -/
theorem hash_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : One K W SP R N A D nl n tl s₀₁) (o₂ : One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64)
    (halen₁ : s₀₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₁.length)
    (halen₂ : s₀₂.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₂.length) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀₁ ∧ s₂ = s₀₂) (Impl.AesOcb.X86_64.hash (callees v)) fun _ _ => True := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  have hr : a₂.length % 16 = a₁.length % 16 := by rw [hal]
  have haad₁ := o₁.sl.aad
  have haad₂ := o₂.sl.aad
  -- The first block.
  have a := (rel_flagsC [] [248] hDW hn (fun s₁ s₂ (h : s₁ = s₀₁ ∧ s₂ = s₀₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, halen₁, halen₂, hal]⟩⟩)
    (c := .block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s 0 ∧ s.zf = some (decide (a₁.length / 16 = 0)))
    (F₂ := fun (s : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s 0 ∧ s.zf = some (decide (a₂.length / 16 = 0)))
    fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hashHead_ok C₁ o₁.env haad₁ halen₁, hashHead_ok C₂ o₂.env haad₂ halen₂⟩
  -- The chunks.
  have lp : RelCT isa (fun s₁ s₂ => ∃ j, a₁.length / 16 - 0 = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (.loop (hashChunk (callees v)) .ne) fun _ _ => True :=
    (RelCT.loop (Q := fun s₁ s₂ => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
        HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16))
      (fun k s₁ s₂ => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (fun k => RelCT.exists_ fun j => chunk_rel v C₁ C₂ o₁ o₂ hal hn k j) _).mono (fun _ _ h => h)
      fun _ _ _ => trivial
  have i₁ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := .loop (hashChunk (callees v)) .ne)
    (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ 0 ∧ s₁.zf = some (decide (a₁.length / 16 = 0))) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ 0 ∧ s₂.zf = some (decide (a₂.length / 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length / 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [h0] at this
      · exact lp.mono (fun s₁ s₂ h => ⟨0, rfl, Nat.pos_of_ne_zero h0, h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
  have X := (RelCT.seq a i₁).wp
    (F₁ := fun s => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s (a₁.length / 16))
    (F₂ := fun s => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s (a₂.length / 16)) fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hashHI_ok v C₁ o₁.env haad₁ halen₁, hashHI_ok v C₂ o₂.env haad₂ halen₂⟩
  -- The rest.
  have t₁ := (rel_flagsC [] [112] hDW hn (fun s₁ s₂ (h : True ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) => by
      have O₁ := h.2.1.one C₁ o₁
      have O₂ := h.2.2.one C₂ o₂
      exact ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (112 : Nat) = tmpO from rfl, h.2.1.rest, h.2.2.rest, hr]⟩⟩)
    (c := .block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (t : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (a₁.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧ t.zf = some (decide (a₁.length % 16 = 0)))
    (F₂ := fun (t : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (a₂.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧ t.zf = some (decide (a₂.length % 16 = 0)))
    fun s₁ s₂ h => ⟨tailHead_ok h.2.1, tailHead_ok h.2.2⟩
  have rr : (0 < a₁.length % 16) → RelCT isa (fun s₁ s₂ =>
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16)))
      (hashRest (callees v)) fun _ _ => True := fun hr0 => by
    have p := (rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h :
        (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
        (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16))) =>
      (⟨(h.1.1.one C₁ o₁).env, (h.2.1.one C₂ o₂).env,
        (h.1.1.one C₁ o₁).sl, (h.2.1.one C₂ o₂).sl, (h.1.1.one C₁ o₁).wr, (h.2.1.one C₂ o₂).wr, fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · rw [h.1.1.rbx, h.2.1.rbx, hM]
          · rw [h.1.2, h.2.2, hr], fun _ h => (nomatch h)⟩ : Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂))
      (c := .seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO))))
      ⟨_, by taint_decide⟩).wp (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨hashRestPre_one C₁ o₁ h.1.1 hr0 h.1.2, hashRestPre_one C₂ o₂ h.2.1 (by omega) h.2.2⟩
    have c := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] [] (args := oneBlock bufO)
      ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 bufO) (k := 1)
      (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
        ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 bufO (by decide), oneBlock_ok h.2.2.env.r15 bufO (by decide),
          dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
      (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨callBuf_one v L C₁.rounds hDW h.2.1, callBuf_one v L C₁.rounds hDW h.2.2⟩
    have e := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ One K W SP R N A D nl n tl s₁ ∧
      One K W SP R N A D nl n tl s₂) => Both.of h.2.1 h.2.2) (c := .block (xor16 .r15 bufO sumO)) ⟨_, by taint_decide⟩
    unfold hashRest
    exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq p (RelCT.seq c e))
  have i₂ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := hashRest (callees v)) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧
        s₁.zf = some (decide (a₁.length % 16 = 0))) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧
        s₂.zf = some (decide (a₂.length % 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length % 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2.2).symm.trans h.2
        simp [h0] at this
      · exact (rr (Nat.pos_of_ne_zero h0)).mono (fun s₁ s₂ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1⟩, ⟨h.1.2.2.1, h.1.2.2.2.1⟩⟩)
          fun _ _ h => h)
  unfold Impl.AesOcb.X86_64.hash
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq X (RelCT.seq t₁ i₂))

end VG.Proof.AesOcb.X86_64
