import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.AesCcm.Words32
import VerifiedGarbage.Proof.AesGcm.X86.Cmp

/-!
# AES-CCM on x86: `Ctr₀`, counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`). `ctrAt` makes `Ctrᵢ` at `W + 64` from `Ctr₀`
(`ctrAt_ok`); `updBlock y` chains the block `B` at `W + 32` into the MAC
state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv LoopPre CopyPost copyLoop_ok zero4_fold zero4_bytes'
  length_bytesAt)

/-! ## `Ctr₀` -/

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {N : BitVec 32} {nl : Nat}
    (hNp : slotv s.mem W nonceO = N) (hnl : slotv s.mem W nlenO = BitVec.ofNat 32 nl) (hN : Buf W SP s N nl)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => Env K W SP s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hz := zero4_fold s.mem W 48
  simp only [Nat.reduceAdd] at hz
  have hb := sub_low_byte32 (show nl ≤ 14 by omega)
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (zero4 c0O ++ [.mov .eax (imm 14), .alu .sub .eax (slot nlenO), .store8 (at_ .ebp c0O) .al,
        .mov .edi (slot nonceO), .mov .edx (.reg .ebp), .alu .add .edx (imm (c0O + 1)), .mov .ecx (slot nlenO)]) s =
        some s₁ ∧
      s₁.mem = (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 48)).writeW (w64 W + BitVec.ofNat 64 48)
        (BitVec.ofNat 8 (15 - nl - 1)) ∧
      s₁.gpr .edi = N ∧ s₁.gpr .edx = W + BitVec.ofNat 32 49 ∧ s₁.gpr .ecx = BitVec.ofNat 32 nl ∧
      s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hnl, hNp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hz, hb]
    · cregs [hNp]
    · cregs [E.ebp]
    · cregs [hnl]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have a49 : w64 (W + BitVec.ofNat 32 49) = w64 W + BitVec.ofNat 64 49 := L.aW (by decide)
  have dNW : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 49, nl⟩ :=
    hN.w.sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₁ N (W + BitVec.ofNat 32 49) nl :=
    ⟨hdi, hdx, hcx, by omega, by omega, hN.wrap, by rw [L.nW (by decide)]; have := L.fw; omega,
      by rw [hrd₁, hwr₁]; exact hN.rd, by rw [a49]; exact E₁.perm.wC (by omega), by rw [a49]; exact dNW⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ P => ?_
  have hfz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem (w64 N) nl = bytesAt s.mem (w64 N) nl :=
    Proof.AesGcm.X86.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.w.sub_right (Lay.wSub (by decide))) (by have := hN.lt; omega)
  refine ⟨E₁.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)]) P.rd P.wr, ?_, ?_,
    by rw [P.rd, hrd₁], by rw [P.wr, hwr₁]⟩
  · refine hfz.trans ?_
    rw [P.mem, a49]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 49) (n := nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have hz' : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), zero4_bytes']
      rfl
    have hl := length_bytesAt s.mem (w64 N) nl
    rw [P.mem, a49, show w64 W + BitVec.ofNat 64 49 = w64 W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by
        rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hz', hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + nl = nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

/-! ## `ctrAt` -/

/-- Four words stored at `p + 64` (`Cmac.store4`), as the code stores them. -/
theorem store4_fold (m : Mem) (p : Addr) (d : Nat) (a b c e : BitVec 32) :
    (((m.writeW (p + BitVec.ofNat 64 d) a).writeW (p + BitVec.ofNat 64 (d + 4)) b).writeW
      (p + BitVec.ofNat 64 (d + 8)) c).writeW (p + BitVec.ofNat 64 (d + 12)) e =
      Cmac.store4 m (p + BitVec.ofNat 64 d) a b c e := by
  simp only [Cmac.store4, add_ofNat_assoc]

/-- A block as its four words. -/
theorem bytesAt_words (m : Mem) (p : Addr) (d : Nat) :
    bytesAt m (p + BitVec.ofNat 64 d) 16 = le4 (m.readW (p + BitVec.ofNat 64 d) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Cmac.bytesAt_split4, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW]

/-- `Ctrᵢ` at `W + 64`, for `i` in `eax`. -/
theorem ctrAt_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) (hax : s.gpr .eax = BitVec.ofNat 32 i) :
    ∃ s', runBlock isa ctrAt s = some s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hf := store4_fold s.mem (w64 W) 64 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
    (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
    (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)
  simp only [Nat.reduceAdd] at hf
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = Cmac.store4 s.mem (w64 W + BitVec.ofNat 64 64) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
        (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
        (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by crun [ctrAt, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_⟩
    · cmems [hax, hf]
    · intro r a b; cregs [a, b]
    all_goals rfl
  refine ⟨s', run, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, ?_, hg, hrd, hwr⟩
  have e := bytesAt_words s.mem (w64 W) 48
  simp only [Nat.reduceAdd] at e
  rw [hc0] at e
  have l12 : (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32) ++ le4 (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) ++
      le4 (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).length = 12 := by
    simp only [List.length_append, Proof.Cmac.length_le4]
  have hw : le4 (s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) = (Spec.Ccm.ctrBlock nonce 0).drop 12 := by
    rw [e, List.drop_left' l12]
  rw [hm, Cmac.bytesAt_store4, show bswap (BitVec.ofNat 32 i) = byteRev32 (BitVec.ofNat 32 i) from rfl,
    ctr_or32 h7 h13 hw hi hi32]
  conv_rhs => rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce i)]
  rw [ctrBlock_take12 h7 h13 hi32, e, List.take_left' l12]

/-! ## Chaining `B` -/

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee v.suffix y) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (w64 W + BitVec.ofNat 64 32) 16] := by
  obtain ⟨s₁, run₁, hm₁, hax, hcx, hdx, hbx, hsi, hdi, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (keyArgs y ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm blkO), .mov .esi (imm 1)] ++ updScr) s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .eax = K ∧ s₁.gpr .ecx = BitVec.ofNat 32 R ∧ s₁.gpr .edx = W + BitVec.ofNat 32 y ∧
      s₁.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s₁.gpr .esi = BitVec.ofNat 32 1 ∧
      s₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [keyArgs, updScr, E.ebp, L.aW, E.perm.wR, hK, hRo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hK]
    · cregs [hRo]
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs []
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have hq := srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨w64 (W + BitVec.ofNat 32 32), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rw [L.aW (o := 32) (by decide)]
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (updCall_ok v L E₁ hR (by omega) hq hqy (by decide) hax hcx hdx hbx hsi hdi)
    fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ⟨E₂, by rw [rd₂, hrd₁], by rw [wr₂, hwr₁], by rw [← hm₁]; exact f₂, ?_⟩
  rw [o₂, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
    (Proof.Cmac.bytesAt_length _ _ _), hm₁, L.aW (o := 32) (by decide)]

end VG.Proof.AesCcm.X86
