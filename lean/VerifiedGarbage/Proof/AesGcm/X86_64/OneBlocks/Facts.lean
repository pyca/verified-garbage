module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot

/-! ### `AesGcm.X86_64.OneBlocks.Ok`, which only this module used -/

section

/-!
# AES-GCM on x86-64: `oneBlocks`

Untrusted: everything here is checked by Lean. `oneBlocks` encrypts
(`oneBlocksE_ok`) or decrypts (`oneBlocksD_ok`) the `⌊n / 16⌋` whole blocks
of the data and absorbs them, from the counter block and the accumulator of
the state, and keeps what is left of the data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom inc32)

/-- The counter block and the accumulator, in the state. -/
abbrev cbA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
abbrev yA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : Gcm.X86_64.Stitch.CtxMode}
include L

/-- The length kept, apart from what the call reads. -/
theorem w192_eqs {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) (v : BitVec 64) :
    let m := s.mem.writeW (W + BitVec.ofNat 64 192) v
    m.readW (W + BitVec.ofNat 64 176) 64 = s.mem.readW (W + BitVec.ofNat 64 176) 64 ∧
    m.readW (W + BitVec.ofNat 64 200) 64 = s.mem.readW (W + BitVec.ofNat 64 200) 64 ∧
    m.readW (W + BitVec.ofNat 64 208) 64 = s.mem.readW (W + BitVec.ofNat 64 208) 64 ∧
    bytesAt m Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) ∧
    blockAt m (cbA W) = blockAt s.mem (cbA W) ∧ blockAt m (yA W) = blockAt s.mem (yA W) ∧
    blocksAt m D (n / 16) = blocksAt s.mem D (n / 16) ∧ blockAt m (Ctx + 240) = blockAt s.mem (Ctx + 240) ∧
    Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem m := by
  intro m
  have ww := L.ww
  have hf : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem m :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have sep : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    fun d h₁ h₂ => Offset.sep _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  refine ⟨Mem.readW_writeW_sep (sep 176 (.inl (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 200 (.inr (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 208 (.inr (by decide)) (by decide)) (by decide),
    bytesAt_frame hf (one ((L.cw'.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))))
      (by have := L.cw; omega_using [hRb]),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega_using []))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega_using [this]),
    blockAt_frame hf (one ((L.cw'.sub_left (Offset.sub_base (d := 240) _ (by decide))).sub_right
      (Lay.wSub (by decide)))),
    hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩⟩

/-- The bookkeeping of `oneBlocks` around its call: from the state `s₁` after
the length is kept to the end, given the call's frame (`hframe`). -/
theorem oneBlocks_core (f : Fn) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s)
    {Out : State → State → Prop}
    (hframe : ∀ s₂, ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s₂ fun s₄ =>
        (∀ r ∈ calleeSaved, s₄.gpr r = s₂.gpr r) ∧ s₄.rd = s₂.rd ∧ s₄.wr = s₂.wr ∧
        Frame (obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s₂.mem s₄.mem ∧ Out s₂ s₄)
    (h0 : n / 16 = 0 → ∀ s₁, s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s s₁)
    (hout : ∀ s₂ s₄ s₅, s₂.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s₂ s₄ →
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s₄.mem s₅.mem → Out s s₅) :
    WP isa (oneBlocks f) s fun s' => ObPost Ctx W SP D n s s' ∧ Out s s' := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, e208, -, -, -, -, -, f192⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.seq (WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have t₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by rw [m₁, Mem.readW_writeW_self64]
  have hf₁ : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₁.mem := by
    rw [m₁]; exact f192.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨⟨he₁, rd₁, wr₁, hf₁, t₁, ?_, ?_⟩, h0 hz s₁ m₁⟩
    · rw [m₁, e200, h.dat, hz]; simp
    · rw [m₁, e208, h.len]; congr 1; omega_using [hz]
  · simp only [decide_eq_false_iff_not] at hz
    have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
    have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
    refine WP.seq (WP.mono (ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    have obi : ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ := ⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by omega_using [], h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, h.rounds.2, h.t_w.sub_right (Lay.wSub (by decide)),
      h.ext.keep (rd₂.trans rd₁) (wr₂.trans wr₁) (by rw [m₂, m₁]; exact f192) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.ext.cw.sub_right (Lay.wSub (by decide)))⟩
    refine WP.seq (WP.mono (hframe s₂ obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₄⟩ => ?_)
    have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₂.keep (fun r hr => cs₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (ob_slots L h.data.ok.w (by omega_using []) h.t_w h₁ h₂) (by decide), m₂]
    have hd₄ : s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [kp 200 (by decide) (by decide), hd₁]
    have hl₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
      rw [kp 208 (by decide) (by decide), m₁, e208, h.len]
    refine WP.mono (ob3_ok hn he₄ hd₄ hl₄) fun s₅ ⟨g₅, d₅, l₅, f₅, rd₅, wr₅⟩ => ?_
    have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => g₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₅ wr₅
    refine ⟨⟨he₅, rd₅.trans (rd₄.trans (rd₂.trans rd₁)), wr₅.trans (wr₄.trans (wr₂.trans wr₁)), ?_, ?_, d₅, l₅⟩,
      hout s₂ s₄ s₅ (m₂.trans m₁) o₄ f₅⟩
    · refine hf₁.trans ?_
      rw [← m₂]
      refine (fr₄.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
      exact f₅.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩
    · rw [f₅.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide),
        kp 192 (by decide) (by decide), t₁]


/-- What encrypting the whole blocks does, from `s` to `s'`. -/
def OutE (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W)) ∧
  blockAt s'.mem (yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (yA W)) (blocksAt s'.mem D q)

/-- What decrypting the whole blocks does, from `s` to `s'`. -/
def OutD (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W)) ∧
  blockAt s'.mem (yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (yA W)) (blocksAt s.mem D q)

/-- The kept slots written after the call are apart from the blocks, the
counter block and the accumulator. -/
theorem ob_after {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) {m m' : Mem}
    (hf : Frame [⟨W + BitVec.ofNat 64 200, 16⟩] m m') :
    blocksAt m' D (n / 16) = blocksAt m D (n / 16) ∧ blockAt m' (cbA W) = blockAt m (cbA W) ∧
    blockAt m' (yA W) = blockAt m (yA W) := by
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 200, 16⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 200, 16⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega_using []))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega_using [this]),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))⟩

/-- `oneBlocks` of the encrypting function. -/
theorem oneBlocksE_ok (B : BlkFn M) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) :
    WP isa (oneBlocks B.enc) s fun s' => ObPost Ctx W SP D n s s' ∧ OutE Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine oneBlocks_core L _ h (fun s₂ hi => obFrameE_ok L B hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [OutE, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃, a₁]; exact o₃⟩

/-- `oneBlocks` of the decrypting function. -/
theorem oneBlocksD_ok (B : BlkFn M) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) :
    WP isa (oneBlocks B.dec) s fun s' => ObPost Ctx W SP D n s s' ∧ OutD Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine oneBlocks_core L _ h (fun s₂ hi => obFrameD_ok L B hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [OutD, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃]; exact o₃⟩

end

end VG.Proof.AesGcm.X86_64

end

end


/-!
# AES-GCM on x86-64: after `oneBlocks`

Untrusted: everything here is checked by Lean. What `seal` and `open` know
after `oneBlocks` (`ob_facts`): the whole blocks of the data in counter mode,
the counter after them, the accumulator over them, and everything else kept.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom ghash blocks inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `seal` and `open` write after their entry, with `oneBlocks`. -/
abbrev oneFrameB (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 192, 32⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 24]

theorem oneFrame_B {W D SP : Addr} {n k : Nat} (hk : k ≤ n) {m m' : Mem}
    (h : Frame (oneFrame W (D + BitVec.ofNat 64 k) SP (n - k)) m m') : Frame (oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_using [hk])⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

theorem obFrame_B {W D SP : Addr} {n : Nat} {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) m m') : Frame (oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

theorem oneB_trans {W D SP : Addr} {n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Frame (oneFrameB W D SP n) m₁ m₂)
    (h₂ : Frame (oneFrameB W D SP n) m₂ m₃) : Frame (oneFrameB W D SP n) m₁ m₃ := h₁.trans h₂

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The kept values are outside `oneFrameB`. -/
theorem kept_oneFrameB {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) (h : (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ oneFrameB W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega_using [h])) (by omega_using [h]) (by decide)
  · exact L.w_w (by omega_using [h]) (by omega_using [h]) (by decide)
  · exact L.w_w (.inl (by omega_using [h])) (by omega_using [h]) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega_using [h]))).symm
  · exact (t_w.sub_right (Lay.wSub (by omega_using [h]))).symm

theorem saved_oneFrameB {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) : ∀ r ∈ oneFrameB W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (t_w.sub_right (Lay.wSub (by decide))).symm

/-- The key context is outside `oneFrameB`. -/
theorem ctx_oneFrameB {D : Addr} {n : Nat} (hC : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) : ∀ r ∈ oneFrameB W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cw'.sub_right (by simpa using Offset.sub_base W (d := 0) (n := 128) (k := 2560) (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact hC
  · exact t_c.symm

/-- The parts of the state `seal` and `open` keep through `oneBlocks`. -/
theorem st_obFrame {D : Addr} {n d k : Nat} (h : (d + k ≤ 16) ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (64 ≤ d ∧ d + k ≤ 80))
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat_assoc]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by omega_using [h])) (by omega_using [h]) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega_using [h]) (by omega_using [h]) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega_using [h]) (by omega_using [h]) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Lay.wSub (by omega_using [h]))).symm
  · exact L.w_w (.inl (by omega_using [h])) (by omega_using [h]) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega_using [h]))).symm

/-- What `seal` and `open` know after `oneBlocks`, from what it did to the
whole blocks (`ho`, `hc`) and the accumulator (`hy`, over `Z`). -/
theorem ob_facts {R : Nat} {D : Addr} {n : Nat} {s s₃ : State} {M : Gcm.X86_64.Stitch.CtxMode} (h : ObPre M Ctx W SP R D n s)
    (fr : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₃.mem)
    {H icb : Block} {x Z : List Byte}
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x) (hx : x.length % 16 = 0)
    (ho : blocksAt s₃.mem D (n / 16) = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem D (n / 16)))
    (hc : blockAt s₃.mem (cbA W) = Nat.repeat inc32 (n / 16) (blockAt s.mem (cbA W)))
    (hZ : Z.length % 16 = 0) (hy : blockAt s₃.mem (yA W) = ghashFrom H (blockAt s.mem (yA W)) (blocks Z)) :
    Frame (oneFrameB W D SP n) s.mem s₃.mem ∧ RoundsAt s₃.mem W R ∧
    blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H ∧ ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R ∧
    blockAt s₃.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) ∧
    bytesAt s₃.mem D (16 * (n / 16)) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D (16 * (n / 16))) ∧
    Ctr s₃.mem (cbA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx R) icb (16 * (n / 16)) ∧
    Absorbed s₃.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (x ++ Z) ∧
    bytesAt s₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
  have hD := h.data.ok.w
  have hR := h.rounds.2
  have hlt := h.data.ok.lt
  have fB := obFrame_B fr
  have dC := ctx_oneFrameB L h.data.ctx h.t_c
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame fB dC hR
  have cw := Proof.Gcm.ctr_whole (ks := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (icb := icb) (n := 0)
    ⟨hcb, fun h => absurd rfl h⟩ rfl ho hc
  rw [Nat.zero_add, ← hc₃] at cw
  refine ⟨fB, rounds_frame fB (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) h.rounds,
    by rw [blockAt_frame fB (fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))), hH], hc₃,
    by simpa using blockAt_frame fr (st_obFrame L (d := 0) (k := 16) (.inl (by decide)) hD h.t_w),
    by rw [cw.1, hc₃], cw.2, Proof.Gcm.absorb_whole habs hx hZ (by rw [hy]), bytesAt_frame fr (fun r hr => ?_) (by omega_using [])⟩
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ := Offset.sub_base D (by omega_using [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · simpa using Offset.disjoint D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (e := 0) (k := n / 16 * 16)
      (.inr (by omega_using [])) (by omega_using [hlt]) (by omega_using [hlt])
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (h.t_d.sub_right hs).symm

end

end VG.Proof.AesGcm.X86_64
