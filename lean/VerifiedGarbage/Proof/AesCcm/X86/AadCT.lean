import VerifiedGarbage.Proof.AesCcm.X86.Aad
import VerifiedGarbage.Proof.AesCcm.X86.AbsorbCT

/-!
# AES-CCM on x86: the associated data is chained in constant time

Untrusted: everything here is checked by Lean. `minLen` and `header` branch
on the length of the associated data, `aadHead` and `aad` also on the
slots holding it and its address: all public (`minLen_ct`, `header_ct`,
`aadHead_ct`, `aad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 minLen dO nO bO)
open VG.Proof.AesGcm.X86 (CT w64 slotv LoopPre copyLoop_ok length_bytesAt)
open VG.Proof.AesCcm (hdrLen headLen)

theorem minLen_ct {I : State → Prop} {K W SP : BitVec 32} (L : Lay K W SP) {n b : Nat}
    (hp : ∀ s, I s → Env K W SP s ∧ slotv s.mem W nO = BitVec.ofNat 32 n ∧ slotv s.mem W bO = BitVec.ofNat 32 b ∧
      b ≤ 16 ∧ n < 2 ^ 32) :
    CT I minLen := by
  refine CT.seq (J := fun s => s.cf = some (decide (n < 16 - b)))
    (CT.taint [.ebp] (pin_ebp fun s h => (hp s h).1.ebp) (by taint_decide)) (fun s hs => ?_)
    (CT.ite (decide (n < 16 - b)) (fun _ h => eval_b h)
      (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)) (fun _ => CT.nil))
  obtain ⟨E, hn, hb, hb16, hnlt⟩ := hp s hs
  obtain ⟨s₁, run₁, -, -, cf, -⟩ := minLen1_ok L E hn hb hb16 hnlt
  exact WP.of_runBlock ⟨s₁, run₁, cf⟩

theorem header_ct {I : State → Prop} {K W SP : BitVec 32} (L : Lay K W SP) {a : Nat} (ha : a < 2 ^ 32)
    (hp : ∀ s, I s → Env K W SP s ∧ slotv s.mem W nO = BitVec.ofNat 32 a) : CT I header := by
  refine CT.seq (J := fun s => s.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧ s.gpr .ebp = W)
    (CT.taint [.ebp] (pin_ebp fun s h => (hp s h).1.ebp) (by taint_decide)) (fun s hs => ?_)
    (CT.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (fun _ h => eval_b h.1)
      (fun _ => by exact CT.taint [.ebp] (pin_ebp fun _ h => h.2) (by taint_decide))
      (fun _ => by exact CT.taint [.ebp] (pin_ebp fun _ h => h.2) (by taint_decide)))
  obtain ⟨s₁, run₁, -, -, cf, bp, -⟩ := headerBlk_ok L (hp s hs).1 ha (hp s hs).2
  exact WP.of_runBlock ⟨s₁, run₁, cf, bp⟩

/-- The slots `header` does not write are kept. -/
theorem header_kept {W : BitVec 32} {m m' : Mem}
    (f : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m m') {o : Nat}
    (ho : 112 ≤ o ∧ o + 4 ≤ 280 ∨ 284 ≤ o ∧ o + 4 ≤ 2560) : slotv m' W o = slotv m W o :=
  f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (by simp only [bO]; omega_arith) (by omega_arith) (by decide)) (by decide)

/-- After `header`: what `PadPre` says, and the length of the encoding at
`W + bO`. -/
structure HeadPre (K W SP : BitVec 32) (R : Nat) (A : BitVec 32) (a : Nat) (s : State) : Prop
    extends PadPre K W SP R A a s where
  b : slotv s.mem W bO = BitVec.ofNat 32 (hdrLen a)

theorem aadHead_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (PadPre K W SP R A a) (aadHead v.callee v.suffix y) := by
  have hh6 : hdrLen a ≤ 6 := by unfold hdrLen; split <;> (try split) <;> omega_arith
  have hn1 : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega_arith
  -- `header`.
  refine CT.seq (J := HeadPre K W SP R A a) (header_ct L ha fun s hs => ⟨hs.env, hs.n⟩)
    (fun s hs => WP.mono (header_ok L hs.env ha hs.n) fun s₁ ⟨E₁, rd, wr, f, hb, _⟩ =>
      ⟨⟨E₁, by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.ctx,
        by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.d,
        by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.n⟩, hb⟩) ?_
  -- `minLen`.
  refine CT.seq (J := fun s => HeadPre K W SP R A a s ∧ s.gpr .ecx = BitVec.ofNat 32 (headLen a))
    (minLen_ct L fun s hs => ⟨hs.env, hs.n, hs.b, by omega_arith, ha⟩)
    (fun s hs => WP.mono (minLen_ok L hs.env hs.n hs.b (by omega_arith) ha) fun s₁ ⟨cx, bp, sp, m, rd, wr⟩ =>
      ⟨⟨⟨⟨bp, sp, hs.env.perm.of_eq rd wr⟩, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [m]; exact hs.d, by rw [m]; exact hs.n⟩, by rw [m]; exact hs.b⟩,
        by rw [cx]; congr 1; unfold headLen; omega_arith⟩) ?_
  -- The arguments of the copy.
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.1.env.ebp) (by taint_decide)
    (fun s ⟨hs, cx⟩ => aadHeadArgs_ok L hs.env hs.d hs.n hs.b cx hn1.2.1 ha) ?_
  -- The copy, then the block chained.
  refine CT.seq (J := fun s₃ => Env K W SP s₃ ∧ slotv s₃.mem W ctxO = K ∧ slotv s₃.mem W roundsO = BitVec.ofNat 32 R)
    (Proof.AesGcm.X86.copyLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))
    (fun s₃ ⟨s₂, ⟨hs, _⟩, hm₃, hdi, hdx, hcx₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ => ?_)
    (updBlock_ct v L hR hy fun _ h => h)
  have E₃ : Env K W SP s₃ := ⟨hbp₃, hsp₃, hs.env.perm.of_eq hrd₃ hwr₃⟩
  have hA₃ := (hs.buf ha0).of_eq hrd₃ hwr₃
  have aB : w64 (W + BitVec.ofNat 32 (32 + hdrLen a)) = w64 W + BitVec.ofNat 64 (32 + hdrLen a) := L.aW (by omega_arith)
  have lp : LoopPre s₃ A (W + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) :=
    ⟨hdi, hdx, hcx₃, hn1.1, by omega_arith, by have := hA₃.wrap; omega_arith, by rw [L.nW (by omega_arith)]; have := L.fw; omega_arith,
      (hA₃.take hn1.2.1).rd, by rw [aB]; exact E₃.perm.wC (by omega_arith),
      by rw [aB]; exact (hA₃.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ P₄ => ?_
  have fC : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [P₄.mem, aB]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega_arith) (by omega_arith)
        (by decide))
  have k₄ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₄.mem W o = slotv s₂.mem W o := fun o h₁ h₂ =>
    (fC.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide)).trans (split_kept hm₃ h₁ h₂)
  exact ⟨E₃.keep (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)]) P₄.rd P₄.wr,
    by rw [k₄ _ (by decide) (by decide)]; exact hs.ctx, by rw [k₄ _ (by decide) (by decide)]; exact hs.rounds⟩

/-- What `aad` starts from. -/
structure AadPre (K W SP : BitVec 32) (R : Nat) (A : BitVec 32) (al : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  aad : slotv s.mem W aadO = A
  alen : slotv s.mem W alenO = BitVec.ofNat 32 al
  buf : Buf W SP s A al

theorem aad_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {al : Nat} (hl : al < 2 ^ 32) :
    CT (AadPre K W SP R A al) (aad v.callee v.suffix y) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => aadBlk_ok L hs.env hs.aad hs.alen hl) ?_
  refine CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : al ≠ 0 := of_decide_eq_false hf
  have hk : headLen al ≤ al := by unfold headLen; omega_arith
  have toPad : ∀ s₁, (∃ s, AadPre K W SP R A al s ∧ s₁.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) A).writeW
      (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 al) ∧ s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) → PadPre K W SP R A al s₁ :=
    fun s₁ ⟨s, hs, hm₁, _, hbp, hsp, hrd₁, hwr₁⟩ =>
      have f₁ : Frame [wC W] s.mem s₁.mem := by
        rw [hm₁]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide)
            (by decide))).writeW (List.mem_singleton_self _) _
          (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
      have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
        f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
          (by decide)
      ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩, by rw [k₁ _ (by decide) (by decide)]; exact hs.ctx,
        by rw [k₁ _ (by decide) (by decide)]; exact hs.rounds, fun _ => hs.buf.of_eq hrd₁ hwr₁,
        by rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
           exact Mem.readW_writeW_self32 _ _ _,
        by rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _⟩
  refine CT.seq (J := PadPre K W SP R (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((aadHead_ct v L hR hy (by omega_arith) hl).mono toPad) (fun s₁ h => ?_) (absorbPad_ct v L hR hy (by omega_arith))
  have P := toPad s₁ h
  obtain ⟨s, hs, -⟩ := h
  refine WP.mono (aadHead_ok v L P.env hR P.ctx P.rounds hy (P.buf (by omega_arith)) (by omega_arith) hl P.d P.n)
    fun s₂ ⟨A₂, hd₂, hn₂⟩ => ⟨A₂.env, by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.ctx,
      by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.rounds, fun _ => ?_, hd₂, hn₂⟩
  have hA := P.buf (by omega_arith)
  exact (hA.drop hk (by have := hA.wrap; omega_arith)).of_eq A₂.rd A₂.wr

end VG.Proof.AesCcm.X86
