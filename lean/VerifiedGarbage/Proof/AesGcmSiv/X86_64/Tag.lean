import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval

/-!
# AES-GCM-SIV on x86-64: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o` encrypts the tag
input at `W + 96` with the encryption key's schedule at `W + 248` into the
block at `W + o`, by `vg_aes_ctr32` of one zero block from a copy of it at
`W + 112` (`tag_ok`); counter mode's last block uses the same code for the
keystream block at `W + 128`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall CtrPost ctr_call toNat_ofNat_of_lt)

theorem blockAt_zero2 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero2 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- A part of `W` read after a write to its start. -/
theorem readW_writeW_W0 {m : Mem} {W : Addr} {d w w' : Nat} (v : BitVec w') (h : w' / 8 ≤ d)
    (hd : d + w / 8 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) (hw' : w' / 8 ≤ 2 ^ 64) :
    (m.writeW W v).readW (W + BitVec.ofNat 64 d) w = m.readW (W + BitVec.ofNat 64 d) w := by
  simpa using readW_writeW_W (m := m) (W := W) (e := 0) (d := d) (w := w) v (.inr (by omega)) hd (by omega) hw

/-- What `tag o` writes. -/
abbrev tagR (W SP : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (K W SP : Addr) (R o : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  frame : Frame (tagR W SP o) t.mem t'.mem
  out : bytesAt t'.mem (W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R (bytesAt t.mem (W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) {o : Nat}
    (ho : o = 0 ∨ o = 128) :
    ∃ t₁ : State, runBlock isa
    (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o) t = some t₁ ∧
    t₁.mem = Proof.Cmac.zero2 ((t.mem.writeW (W + BitVec.ofNat 64 112) (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW
      (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64))
      (W + BitVec.ofNat 64 o) ∧
    t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
    t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧ t₁.gpr .rcx = W + BitVec.ofNat 64 o ∧
    t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 1768 ∧
    (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3816 by decide)
  have z₀ := E.perm.wW (show o + 8 ≤ 3816 by omega)
  have z₈ := E.perm.wW (show o + 8 + 8 ≤ 3816 by omega)
  rcases ho with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd, BitVec.add_zero] at z₀ z₈
    refine ⟨_, by srun [copy16, zero16, ctrArgs, h15, rR, rR', r₀, r₈, w₀, w₈, z₀, z₈, readW_writeW_W0], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.zero2, add_ofNat_assoc, BitVec.add_zero, Nat.reduceAdd]; rfl
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR,
      BitVec.add_zero]; done)
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl

theorem tag_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) {o : Nat}
    (ho : o = 0 ∨ o = 128) :
    WP isa (tag v.callees o) t (TagPost K W SP R o t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := tagArgs_ok L E S ho
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have dO : (⟨W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc : CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
      (W + BitVec.ofNat 64 1768) R 1 :=
    cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide) (srcW L E₁.perm (t := o) (k := 16 * 1) (by omega))
      dO (L.w_w (.inr (by omega)) (by decide) (by omega)) (E₁.perm.wC (by omega)) rdi rsi rdx rcx r8 r9
  have fZ := Proof.Cmac.frame_store2 (m := (t.mem.writeW (W + BitVec.ofNat 64 112)
    (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8)
    (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)) (W + BitVec.ofNat 64 o) 0 0
  have fC := Proof.Cmac.frame_store2 (m := t.mem) (W + BitVec.ofNat 64 112)
    (t.mem.readW (W + BitVec.ofNat 64 96) 64) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact (fC.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero2, Proof.AesGcm.X86_64.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide),
      Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact blockAt_zero2 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by omega)) (by decide) (by omega))
      (by rcases hR with h | h <;> subst h <;> decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp, Nat.mul_one] at fc
  refine ⟨E₁.of_saved P.saved P.rd P.wr, by rw [P.rd, hrd₁], by rw [P.wr, hwr₁],
    fun r hr => by rw [P.saved r hr, hg₁ r hr],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith R (bytesAt t₁.mem (W + BitVec.ofNat 64 248) (16 * (R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.X86_64
