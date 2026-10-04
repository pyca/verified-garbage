import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Callee
import VerifiedGarbage.Proof.GcmSiv.Spec

/-!
# AES-GCM-SIV on x86-64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 128` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i`: after the loop, the halves of `derive_keys`
(`derive_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call GcmImpl in_off ofNat_add_ofNat)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hN : Buf K W SP t N 12) {i : Nat} (hbx : t.gpr .rbx = BitVec.ofNat 64 i) :
    ∃ t₁ : State, runBlock isa (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO) t = some t₁ ∧
      t₁.mem = ((Proof.Cmac.store4 t.mem (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
          (t.mem.readW N 32) (t.mem.readW (N + BitVec.ofNat 64 4) 32) (t.mem.readW (N + BitVec.ofNat 64 8) 32)).writeW
          (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136) (0 : BitVec 64) ∧
      t₁.gpr .rdi = K ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 128 ∧ t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 2048 ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rN := S.nonce
  have rR := S.rounds
  have n₀ := in_off (d := 0) (n := 4) hN.rd (by decide) (by decide)
  have n₄ := in_off (d := 4) (n := 4) hN.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hN.rd (by decide) (by decide)
  simp only [BitVec.add_zero] at n₀
  have rS := E.perm.wR (show 280 + 8 ≤ 4096 by decide)
  have rR' := E.perm.wR (show 272 + 8 ≤ 4096 by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 4096 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 4096 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 4096 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 4096 by decide)
  have w₅ := E.perm.wW (show 128 + 8 ≤ 4096 by decide)
  have w₆ := E.perm.wW (show 136 + 8 ≤ 4096 by decide)
  refine ⟨_, by srun [deriveBlock, zero16, ctrArgs, h15, rN, rR, n₀, n₄, n₈, rS, rR', w₁, w₂, w₃, w₄, w₅, w₆, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E.r13]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · rfl
  · rfl
  simp only [mem_setReg, mem_arithFlags, Proof.Cmac.store4, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
  rw [add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  simp only [Nat.reduceAdd, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  rfl

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes {W : Addr} (_hw : W.toNat + 4096 ≤ 2 ^ 64) (m : Mem) (N : Addr) (i : Nat) :
    bytesAt (((Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
          (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
          (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136) (0 : BitVec 64))
        (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  have c₁ : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (W + BitVec.ofNat 64 128) (64 / 8) :=
    Offset.contains W (d := 128) (n := 8) (e := 128) (k := 16) (by decide) (by decide) (by omega)
  have c₂ : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (W + BitVec.ofNat 64 136) (64 / 8) :=
    Offset.contains W (d := 136) (n := 8) (e := 128) (k := 16) (by decide) (by decide) (by omega)
  rw [Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by omega) (by omega)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block {W : Addr} (X : Mem) :
    Spec.Gcm.blockAt ((X.writeW (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136)
      (0 : BitVec 64)) (W + BitVec.ofNat 64 128) = 0 := by
  rw [Spec.Gcm.blockAt, show W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 by
    rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2]
  decide

/-- What `derive` writes. -/
abbrev derR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 32⟩, ⟨W + BitVec.ofNat 64 2048, 2048⟩, below SP 8]

theorem derR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ derR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (K W SP : Addr) (σ : State) (R : Nat) (N : Addr) (cnt i : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 cnt
  r12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)
  le : i ≤ cnt
  frame : Frame (derR W SP) σ.mem t.mem
  out : bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem K R) (bytesAt σ.mem N 12) i

/-- The code after the call of a step. -/
abbrev derPost : List Instr :=
  [.mov .rax (.mem (at_ .r15 bO)), .store (at_ .r12 0) .rax, .alu .add .r12 (imm 8), .alu .add .rbx (imm 1),
    .alu .cmp .rbx (.reg .rbp)]

theorem derPost_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {i cnt : Nat} (hi : i < cnt) (hc : cnt ≤ 6)
    (hbx : t.gpr .rbx = BitVec.ofNat 64 i) (hbp : t.gpr .rbp = BitVec.ofNat 64 cnt)
    (h12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)) :
    ∃ t' : State, runBlock isa derPost t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (W + BitVec.ofNat 64 128) 64) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .rbp = BitVec.ofNat 64 cnt ∧
      t'.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * (i + 1)) ∧ t'.zf = some (decide (i + 1 = cnt)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have rb := E.perm.wR (show 128 + 8 ≤ 4096 by decide)
  have wo := E.perm.wW (d := 16 + 8 * i) (n := 8) (by omega)
  refine ⟨_, by srun [derPost, h15, h12, rb, wo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx, ofNat_add_ofNat]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12, add_ofNat_assoc]
    rw [show 16 + 8 * i + 8 = 16 + 8 * (i + 1) by omega]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx, hbp,
      ofNat_add_ofNat, Proof.AesGcm.X86_64.sub_beq (show i + 1 < 2 ^ 64 by omega) (show cnt < 2 ^ 64 by omega)]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- Buffers outside `W` and the stack below `SP` are kept by `derive`. -/
theorem buf_derR {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (derR W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {m m' : Mem}
    (hf : Frame (derR W SP) m m') : Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.stk_k.symm) (by rcases hR with h | h <;> subst h <;> decide)

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (S : Slots W R N A D al n σ.mem) (hN : Buf K W SP σ N 12)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) {cnt i : Nat} (hc : cnt ≤ 6) (hi : i < cnt) {t : State}
    (I : DInv K W SP σ R N cnt i t) :
    WP isa (.seq (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO))
      (.seq (callCtr v.callees) (.block derPost))) t fun t' =>
      DInv K W SP σ R N cnt (i + 1) t' ∧ t'.zf = some (decide (i + 1 = cnt)) := by
  have St := slots_mut L hDW (I.frame.sub (derR_mut W SP D n)) S
  have eN : bytesAt t.mem N 12 = bytesAt σ.mem N 12 := buf_derR hN I.frame
  have eK : Spec.GcmSiv.ctxCiph t.mem K R = Spec.GcmSiv.ctxCiph σ.mem K R := ciph_derR L hR I.frame
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ :=
    derArgs_ok I.env St (hN.of_eq I.rd I.wr) I.rbx
  have E₁ : Env K W SP t₁ := I.env.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    hrd₁ hwr₁
  have cc : CtrCall t₁ K (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 128) (W + BitVec.ofNat 64 2048) R 1 :=
    cargs L E₁ hR (keyK L E₁.perm) (c := 112) (by decide) (srcW L E₁.perm (t := 128) (k := 16 * 1) (by decide))
      (L.w_w (.inr (by decide)) (by decide) (by decide)) (L.k_w' (by decide)) (E₁.perm.wC (by decide))
      rdi rsi rdx rcx r8 r9
  -- The bytes the call is given.
  have hb₁ : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem N 12 := by
    rw [hm₁]; exact derBlock_bytes L.ww _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 128) = 0 := by rw [hm₁]; exact derZero_block _
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 32⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 128) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 136) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_)
  have E₂ : Env K W SP t₂ := E₁.of_saved P.saved P.rd P.wr
  have g₂ : ∀ r ∈ [Reg.rbx, .rbp, .r12], t₂.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [P.saved _ (by decide), hg₁ _ (by simp)]
  obtain ⟨t₃, run₃, hm₃, bx₃, bp₃, r12₃, zf₃, hg₃, hrd₃, hwr₃⟩ :=
    derPost_ok E₂ hi hc (by rw [g₂ _ (by simp), I.rbx]) (by rw [g₂ _ (by simp), I.rbp])
      (by rw [g₂ _ (by simp), I.r12])
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep hg₃ hrd₃ hwr₃, by rw [hrd₃, P.rd, hrd₁, I.rd],
    by rw [hwr₃, P.wr, hwr₁, I.wr], bx₃, bp₃, r12₃, by omega, ?_, ?_⟩, zf₃⟩
  · -- The frame.
    have fc := P.frame
    rw [E₁.rsp] at fc
    refine (I.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)).trans
      ((fc.sub fun r hr => ?_).trans (by
        rw [hm₃]
        exact (Frame.refl _ _).writeW (List.mem_cons_self) _ (Offset.contains W (d := 16 + 8 * i) (n := 8)
          (e := 16) (k := 48) (by omega) (by omega) (by have := L.ww; omega))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · -- The bytes.
    have fc := P.frame
    rw [E₁.rsp] at fc
    have dW : ∀ {d k : Nat}, d + k ≤ 4096 → 16 + 8 * i ≤ d →
        (⟨W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (.inl (by omega)) (by omega) h₁
    have keep : bytesAt t₃.mem (W + BitVec.ofNat 64 16) (8 * i) = bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self (W + BitVec.ofNat 64 (16 + 8 * i)) 8))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.X86_64.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact (L.stk_w' (by omega)).symm) (by omega),
        Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (by omega)) (by omega)]
    have hout := P.out
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem K R (Spec.GcmSiv.le32 i ++ bytesAt σ.mem N 12)).take 8 := by
      have e16 : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 =
          bytesAt t₂.mem (W + BitVec.ofNat 64 128) 8 ++ bytesAt t₂.mem (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem K R = Spec.GcmSiv.ctxCiph t.mem K R :=
        ctxCiph_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide))
          (by rcases hR with h | h <;> subst h <;> decide)
      rw [hm₃, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW,
        show bytesAt t₂.mem (W + BitVec.ofNat 64 128) 8 = (bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith R (bytesAt t₁.mem K (16 * (R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem K R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

theorem shr1 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The start of `derive`: no block yet, and the number of blocks,
`rounds / 2 − 1`. -/
theorem derInit_ok {K W SP : Addr} {σ : State} (E : Env K W SP σ) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n σ.mem) :
    WP isa (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) σ
      (DInv K W SP σ R N (R / 2 - 1) 0) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 272 + 8 ≤ 4096 by decide)
  obtain ⟨t, run, hm, bx, bp, h12, hg, hrd, hwr⟩ : ∃ t : State, runBlock isa ([.mov32 .rbx (imm 0)] ++ ptr .r12 .r15 akO ++
      [.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)]) σ = some t ∧
      t.mem = σ.mem ∧ t.gpr .rbx = BitVec.ofNat 64 0 ∧ t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1) ∧
      t.gpr .r12 = W + BitVec.ofNat 64 16 ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t.gpr r = σ.gpr r) ∧
      t.rd = σ.rd ∧ t.wr = σ.wr := by
    refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, execShift]
      rw [shr1 R (by omega), Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨t, run, E.keep hg hrd hwr, hrd, hwr, bx, bp, by rw [h12], Nat.zero_le _,
    by rw [hm]; exact Frame.refl _ _, rfl⟩

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) :
    WP isa (derive v.callees) σ (DInv K W SP σ R N (R / 2 - 1) (R / 2 - 1)) := by
  have hc : R / 2 - 1 ≤ 6 := by omega
  refine WP.seq (WP.mono (derInit_ok E hR S) fun t I₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧
    DInv K W SP σ R N (R / 2 - 1) i t) ?_ ((R / 2 - 1) - 0) t ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_ok v L hR S hN hDW hc hi I) fun t' ⟨I', hz⟩ => ?_
  by_cases he : i + 1 = R / 2 - 1
  · left; exact ⟨(eval_ne hz).trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), (R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {K W SP : Addr} {σ : State} {R : Nat} (hR : R = 10 ∨ R = 14) {N : Addr} {t : State}
    (I : DInv K W SP σ R N (R / 2 - 1) (R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12) =
      (bytesAt t.mem (W + BitVec.ofNat 64 16) 16, bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R)) := by
  have hk : Spec.GcmSiv.keyLen R / 8 + 2 = R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (R / 2 - 1) = 16 + Spec.GcmSiv.keyLen R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem K R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.X86_64
