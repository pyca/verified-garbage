module

import VerifiedGarbage.Proof.AesCcm.X86.Aad
public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
public import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesCcm.X86.Aad
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesCcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesCcm.X86.Callee
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesCcm.X86.AbsorbCT`, which only this module used -/

section

/-!
# AES-CCM on x86: `absorbPad y` is constant time

Untrusted: everything here is checked by Lean. What `absorbPad` starts from
(`PadPre`) is public: the pointers and the length it branches on, and the
slots holding them; its pieces are constant time from it (`absorbWhole_ct`,
`absorbTail_ct`, `absorbPad_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv WEnv padLoop_ok)

/-- The slots are kept when `dO` and `nO` are written. -/
theorem dn_kept {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) {o : Nat}
    (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o := by
  have f₁ : Frame [wC W] m m' := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
    (by decide)

/-- `dO` and `nO`, after they are written. -/
theorem dn_read {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) :
    slotv m' W dO = a ∧ slotv m' W nO = b := by
  subst hm
  refine ⟨?_, Mem.readW_writeW_self32 _ _ _⟩
  rw [slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

/-- What `absorbPad` of the `len` bytes at `P` starts from. -/
structure PadPre (K W SP : BitVec 32) (R : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < len → Buf W SP s P len
  d : slotv s.mem W dO = P
  n : slotv s.mem W nO = BitVec.ofNat 32 len

/-- The arguments of the call chaining the whole blocks, from `ebp` and
`edi`. -/
theorem wholeArgs_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop} {c : Prog isa} {F : State → State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp, .edi], s₁.gpr r = s₂.gpr r)
    (blk : ∀ s, I s → ∃ s', runBlock isa (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr) s = some s' ∧ F s s')
    (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) c) := by
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂

theorem absorbWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (PadPre K W SP R P len) (.seq (.block splitWhole)
        (.ite .e (.block []) (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) (updCall v.callee v.suffix)))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => split_ok L hs.env hs.d hs.n hl) ?_
  refine CT.ite (decide (len / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine wholeArgs_ct hy (pin2 fun _ ⟨_, _, _, hdi, _, hbp, _⟩ => ⟨hbp, hdi⟩)
    (fun s₁ ⟨s, hs, hbx, hdi, _, hbp, hsp, hm₁, hrd₁, hwr₁⟩ =>
      wholeArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩
        (by rw [split_kept hm₁ (by decide) (by decide)]; exact hs.ctx)
        (by rw [split_kept hm₁ (by decide) (by decide)]; exact hs.rounds) hbx hdi y) ?_
  refine updCall_ct v L hR (y := y) (Q := P) (n := len / 16) (by rcases hy with rfl | rfl <;> decide) (by omega_using [hl])
    fun s₂ ⟨s₁, ⟨s, hs, _, _, _, _, _, _, hrd₁, hwr₁⟩, _, ax, cx, dx, bx, si, di, bp, sp, rd₂, wr₂⟩ => ?_
  have hP := hs.buf (by omega_using [h0])
  exact ⟨⟨bp, sp, hs.env.perm.of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])⟩,
    srcBuf ((hP.take hb).of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])),
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by rcases hy with rfl | rfl <;> decide)),
    ax, cx, dx, bx, si, di⟩

/-- What the last bytes' piece starts from. -/
structure TailPre (K W SP : BitVec 32) (R : Nat) (Q : BitVec 32) (t : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < t → Buf W SP s Q t
  d : slotv s.mem W dO = Q
  n : slotv s.mem W nO = BitVec.ofNat 32 t

theorem absorbTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : BitVec 32} {t : Nat} (ht : t < 16) :
    CT (TailPre K W SP R Q t) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block [])
          (.seq (.block (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
              .mov .ecx (slot nO)] : List Instr)))
            (.seq copyLoop (updBlock v.callee v.suffix y))))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => testN_ok L hs.env (r := t) (by omega_using [ht]) hs.n) ?_
  refine CT.ite (decide (t = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : t ≠ 0 := of_decide_eq_false hf
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, hm₁, _, hbp, hsp, hrd₁, hwr₁⟩ =>
      tailArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩ (Q := Q) (t := t) (by rw [hm₁]; exact hs.d)
        (by rw [hm₁]; exact hs.n)) ?_
  refine CT.seq (J := fun s₃ => Env K W SP s₃ ∧ slotv s₃.mem W ctxO = K ∧ slotv s₃.mem W roundsO = BitVec.ofNat 32 R)
    (Proof.AesGcm.X86.copyLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))
    (fun s₂ ⟨s₁, ⟨s, hs, hm₁, _, _, _, hrd₁, hwr₁⟩, hm₂, hdi, hdx, hcx, hbp₂, hsp₂, hrd₂, hwr₂⟩ => ?_)
    (updBlock_ct v L hR hy fun _ h => h)
  have hB := hs.buf (by omega_using [h0])
  have he : WEnv W s₂ := ⟨hbp₂, by rw [hwr₂, hwr₁]; exact hs.env.perm.w, L.fw⟩
  refine WP.mono (padLoop_ok (S := Q) (d := 32) (t := t) (m := s₁.mem) he hm₂ hdi hdx hcx (by omega_using [h0])
    (by omega_using [ht]) (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hB.rd) hB.wrap (hB.w.sub_right (Lay.wSub (by decide)))
    (by decide)) fun s₃ ⟨_, f₃, g₃, rd₃, wr₃⟩ => ?_
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [← hm₁]
    exact f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide))
      (by decide)
  exact ⟨⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hbp₂],
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hsp₂],
      hs.env.perm.of_eq (by rw [rd₃, hrd₂, hrd₁]) (by rw [wr₃, hwr₂, hwr₁])⟩,
    by rw [k₃ _ (by decide) (by decide)]; exact hs.ctx, by rw [k₃ _ (by decide) (by decide)]; exact hs.rounds⟩

theorem absorbPad_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (PadPre K W SP R P len) (absorbPad v.callee v.suffix y) := by
  refine RelCT.assoc (CT.seq (J := TailPre K W SP R (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16))
    (absorbWhole_ct v L hR hy hl)
    (fun s hs => WP.mono (absorbWhole_ok v L hs.env hR hs.ctx hs.rounds hy hs.buf hl hs.d hs.n)
      fun s₁ ⟨A₁, hd₁, hn₁⟩ => ⟨A₁.env, by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.ctx,
        by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.rounds, fun h => ?_, hd₁, hn₁⟩)
    (absorbTail_ct v L hR hy (Nat.mod_lt _ (by decide))))
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hP := hs.buf (by omega_using [h])
  have := (hP.drop hb (by have := hP.wrap; omega_using [h, this])).of_eq A₁.rd A₁.wr
  rwa [show len - 16 * (len / 16) = len % 16 by omega_using []] at this

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the associated data is chained in constant time

Untrusted: everything here is checked by Lean. `minLen` and `header` branch
on the length of the associated data, `aadHead` and `aad` also on the
slots holding it and its address: all public (`minLen_ct`, `header_ct`,
`aadHead_ct`, `aad_ct`).
-/

@[expose] public section

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
    · exact Lay.w_w (.inr (by omega_using [ho])) (by omega_using [ho]) (by decide)
    · exact Lay.w_w (by simp only [bO]; omega_using [ho]) (by omega_using [ho]) (by decide)) (by decide)

/-- After `header`: what `PadPre` says, and the length of the encoding at
`W + bO`. -/
structure HeadPre (K W SP : BitVec 32) (R : Nat) (A : BitVec 32) (a : Nat) (s : State) : Prop
    extends PadPre K W SP R A a s where
  b : slotv s.mem W bO = BitVec.ofNat 32 (hdrLen a)

theorem aadHead_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (PadPre K W SP R A a) (aadHead v.callee v.suffix y) := by
  have hh6 : hdrLen a ≤ 6 := by unfold hdrLen; split <;> (try split) <;> omega_using []
  have hn1 : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega_using [ha0, hh6]
  -- `header`.
  refine CT.seq (J := HeadPre K W SP R A a) (header_ct L ha fun s hs => ⟨hs.env, hs.n⟩)
    (fun s hs => WP.mono (header_ok L hs.env ha hs.n) fun s₁ ⟨E₁, rd, wr, f, hb, _⟩ =>
      ⟨⟨E₁, by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.ctx,
        by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.d,
        by rw [header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.n⟩, hb⟩) ?_
  -- `minLen`.
  refine CT.seq (J := fun s => HeadPre K W SP R A a s ∧ s.gpr .ecx = BitVec.ofNat 32 (headLen a))
    (minLen_ct L fun s hs => ⟨hs.env, hs.n, hs.b, by omega_using [hh6], ha⟩)
    (fun s hs => WP.mono (minLen_ok L hs.env hs.n hs.b (by omega_using [hh6]) ha) fun s₁ ⟨cx, bp, sp, m, rd, wr⟩ =>
      ⟨⟨⟨⟨bp, sp, hs.env.perm.of_eq rd wr⟩, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [m]; exact hs.d, by rw [m]; exact hs.n⟩, by rw [m]; exact hs.b⟩,
        by rw [cx]; congr 1; unfold headLen; omega_using []⟩) ?_
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
  have aB : w64 (W + BitVec.ofNat 32 (32 + hdrLen a)) = w64 W + BitVec.ofNat 64 (32 + hdrLen a) := L.aW (by omega_using [hh6])
  have lp : LoopPre s₃ A (W + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) :=
    ⟨hdi, hdx, hcx₃, hn1.1, by omega_using [hn1], by have := hA₃.wrap; omega_using [hn1, this], by rw [L.nW (by omega_using [hh6])]; have := L.fw; omega_using [hn1, this],
      (hA₃.take hn1.2.1).rd, by rw [aB]; exact E₃.perm.wC (by omega_using [hn1]),
      by rw [aB]; exact (hA₃.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right (Lay.wSub (by omega_using [hn1]))⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ P₄ => ?_
  have fC : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [P₄.mem, aB]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega_using []) (by omega_using [hn1])
        (by decide))
  have k₄ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₄.mem W o = slotv s₂.mem W o := fun o h₁ h₂ =>
    (fC.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide))
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
  have hk : headLen al ≤ al := by unfold headLen; omega_using []
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
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide))
          (by decide)
      ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩, by rw [k₁ _ (by decide) (by decide)]; exact hs.ctx,
        by rw [k₁ _ (by decide) (by decide)]; exact hs.rounds, fun _ => hs.buf.of_eq hrd₁ hwr₁,
        by rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
           exact Mem.readW_writeW_self32 _ _ _,
        by rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _⟩
  refine CT.seq (J := PadPre K W SP R (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((aadHead_ct v L hR hy (by omega_using [h0]) hl).mono toPad) (fun s₁ h => ?_) (absorbPad_ct v L hR hy (by omega_using [hl]))
  have P := toPad s₁ h
  obtain ⟨s, hs, -⟩ := h
  refine WP.mono (aadHead_ok v L P.env hR P.ctx P.rounds hy (P.buf (by omega_using [h0])) (by omega_using [h0]) hl P.d P.n)
    fun s₂ ⟨A₂, hd₂, hn₂⟩ => ⟨A₂.env, by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.ctx,
      by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.rounds, fun _ => ?_, hd₂, hn₂⟩
  have hA := P.buf (by omega_using [h0])
  exact (hA.drop hk (by have := hA.wrap; omega_arith)).of_eq A₂.rd A₂.wr

end VG.Proof.AesCcm.X86
