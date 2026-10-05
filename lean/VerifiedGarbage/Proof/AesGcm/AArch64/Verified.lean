import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.FinTag`. -/
section

/-!
# AES-GCM on AArch64: the tag of a whole message (`finBody`)

Untrusted: everything here is checked by Lean. `finBody o` pads and absorbs
the buffered bytes (of the text, or of the additional data if there is no
text), and writes `GHASH(…, lengths) ⊕ CIPH_K(J₀)` to `W + o`: the tag of the
message (`finBody_ok`, `Proof.Gcm.fullTag_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod_left (a c : Nat) : lensBlock (a % 2 ^ 64) c = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2; omega

/-- The buffered bytes: of the additional data if there is no text. -/
theorem ghashInput_mod {a c : List Byte} : (ghashInput a c).length % 16 =
    if c.length = 0 then a.length % 16 else c.length % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · have hl : c.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_of_ne hc, ite_eq_right hl]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

/-- The regions `finBody o` writes. -/
abbrev finFrame (St W : Addr) (o : Nat) : List Region := tFrame St W 16 ++ tagFrame St W o

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

omit L in
/-- The offset of the buffered bytes. -/
theorem finOff_ok {s : State} {A P : Nat} (h26 : s.gpr .x26 = BitVec.ofNat 64 A)
    (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    WP isa (.ite (.zero .x .x27) (.block [imm .x9 15, .logic .and .x .x25 .x26 .x9])
      (.block [imm .x9 15, .logic .and .x .x25 .x27 .x9])) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (if P = 0 then A % 16 else P % 16) ∧ Regs [.x9, .x25] s s' := by
  refine WP.ite (decide (P = 0)) (eval_zero h27 hP) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P = 0 := by simpa using ht
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h26, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hA]
  · have h0 : P ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hP]

/-- `finBody o`: the tag of the message `a`, `c` into `W + o`. -/
theorem finBody_ok (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k : Reg → BitVec 64} {R : Nat}
    {a c : List Byte} {H : Block} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 a.length) (h27 : s.gpr .x27 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (finBody v.callees o) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      Frame (VG.Proof.AesGcm.AArch64.finFrame St W o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (padded a c))) [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem Ctx R (blockAt s.mem St))) := by
  have hA : a.length % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have h26' : s.gpr .x26 = BitVec.ofNat 64 (a.length % 2 ^ 64) := by rw [h26]; apply BitVec.eq_of_toNat_eq; simp
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finOff_ok h26' h27 hA hc) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := he.of_regs r₁
  have hk₁ := hk.of_others r₁.others
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 ((ghashInput a c).length % 16) := by
    rw [x25₁, VG.Proof.AesGcm.AArch64.ghashInput_mod]
    by_cases h0 : c.length = 0
    · rw [ite_eq_left h0, ite_eq_left h0, Nat.mod_mod_of_dvd _ (by decide)]
    · rw [ite_eq_right h0, ite_eq_right h0]
  refine WP.seq (WP.mono (flush_ok L (.inr rfl) v (H := H) (x := ghashInput a c) he₁ hk₁ h25 rfl
    (by rw [r₁.mem]; exact hH)) fun s₂ ⟨h₂, hH₂, abs₂⟩ => ?_)
  have h22₂ : s₂.gpr .x22 = BitVec.ofNat 64 R := by
    rw [h₂.kept .x22 (by decide), ← hk .x22 (by decide), h22]
  refine WP.mono (tag_ok L v ho h₂.env h₂.kept h22₂ hR h₂.x25) fun s₃ h₃ => ⟨h₃.env, h₃.kept, ?_, fun ha => ?_⟩
  · rw [← r₁.mem]
    exact (h₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  · have f₂ := h₂.frame
    rw [r₁.mem] at f₂ abs₂
    have hacc := Proof.Gcm.Absorbed.whole_eq (abs₂ ha) (Proof.Gcm.length_padded a c)
    rw [h₃.out, hH₂, hacc]
    have h26₂ : (s₂.gpr .x26).toNat = a.length % 2 ^ 64 := by
      rw [h₂.kept .x26 (by decide), ← hk .x26 (by decide), h26', toNat_ofNat_of_lt hA]
    have h27₂ : (s₂.gpr .x27).toNat = c.length := by
      rw [h₂.kept .x27 (by decide), ← hk .x27 (by decide), h27, toNat_ofNat_of_lt hc]
    rw [h26₂, h27₂, VG.Proof.AesGcm.AArch64.lensBlock_mod_left, ciph_frame f₂ (ctx_tFrame' L) hR,
      blockAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
        · exact st0_w L ⟨by decide, by decide⟩)]
    rfl

theorem saved_finFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ VG.Proof.AesGcm.AArch64.finFrame St W o, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_tagFrame L ho r hr


end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT`. -/
section

/-!
# AES-GCM on AArch64: the pieces are constant time

Untrusted: everything here is checked by Lean. Each piece run from two states
that its correctness proof describes with the same public values (the
addresses, lengths and offsets) leaks the same: its code between calls by the
taint analysis, from the registers those proofs pin, and its calls by their
callees' proofs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ofBytes)
open VG.Proof.Gcm (lensBlock)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem absorb_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {x₁ x₂ : List Byte} {D : Addr} {n o : Nat} {σ₁ σ₂ : State}
    (h₁ : AbsIn Ctx St W SP k₁ H₁ x₁ D n o σ₁) (h₂ : AbsIn Ctx St W SP k₂ H₂ x₂ D n o σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (absorb v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24, .x25]) (absSeg1 yo) h).isSome = true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24]) (.block (absSeg2 yo)) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24, h₁.x25, h₂.x25]) t₁)
    (absSeg1_ok L hyo h₁) (absSeg1_ok L hyo h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (absCall1_ok L hyo v a₁ h₁.ho h₁.hH) (absCall1_ok L hyo v a₂ h₂.ho h₂.hH) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24]) t₂)
    (absSeg2_ok L hyo b₁) (absSeg2_ok L hyo b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (absCall2_ok L hyo v c₁) (absCall2_ok L hyo v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.1.env.sp, d₂.1.env.sp])
    (by agree_tac [d₁.1.env.x20, d₂.1.env.x20, d₁.1.x23, d₂.1.x23, d₁.1.x24, d₂.1.x24]) ⟨_, by taint_decide⟩

/-- `flush yo` of `o` bytes. -/
theorem flush_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {o : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o) (ho : o < 16) :
    RelCT isa (Eq2 σ₁ σ₂) (flush v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x25]) (padSeg yo [ptr .x12 .x20 32]) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pad : ∀ {k : Reg → BitVec 64} {σ : State}, Env Ctx St W SP σ → Kept k σ → σ.gpr .x25 = BitVec.ofNat 64 o →
      WP isa (padSeg yo [ptr .x12 .x20 32]) σ (Pad1 Ctx St W SP k yo o (St + BitVec.ofNat 64 32) σ.mem) :=
    fun he hk h25 => padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 ho
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      (covers_left (he.perm.stC (by omega))) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x25] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21, h25₁, h25₂]) t₁)
    (pad he₁ hk₁ h25₁) (pad he₂ hk₂ h25₂) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `lens yo ra rb`. -/
theorem lens_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k₁ k₂ : Reg → BitVec 64} {o₁ o₂ : Nat} {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂)
    (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂)
    (ht : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (lensSeg yo ra rb)) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (lens v.callees yo ra rb) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21]) ht)
    (lensSeg_ok L hyo he₁ hk₁ h25₁ hrb) (lensSeg_ok L hyo he₂ hk₂ h25₂ hrb) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `crypt`. -/
theorem crypt_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ R P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ R P D n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k R P D n σ) {m' : Mem},
      Frame (crFrame St W D n) σ.mem m' → ciphOf m' Ctx R = ciphOf σ.mem Ctx R :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data) h.rounds
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x22, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x22, h₂.x22,
        h₁.x23, h₂.x23, h₁.x24, h₂.x24, h₁.x25, h₂.x25]) ⟨_, by taint_decide⟩)
    (crSeg1_ok L (icb := 0) h₁) (crSeg1_ok L (icb := 0) h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x22, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x22, b₂.1.x22, b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2_ok L b₁.1 b₁.2) (crSeg2_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24]) ⟨_, by taint_decide⟩

/-- `lens yo ra rb`, run. -/
theorem lens_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k : Reg → BitVec 64} {o : Nat} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 o) :
    WP isa (lens v.callees yo ra rb) s (TOut Ctx St W SP k yo o
      (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (St + BitVec.ofNat 64 yo))
        [ofBytes (lensBlock (s.gpr ra).toNat (s.gpr rb).toNat)]) s.mem) :=
  WP.seq (WP.mono (lensSeg_ok L hyo he hk h25 hrb) fun _ h₁ => lensCall_ok L hyo v h₁)

/-- `tag o`. -/
theorem tag_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {R o₁ o₂ : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h22₁ : σ₁.gpr .x22 = BitVec.ofNat 64 R) (h22₂ : σ₂.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂) :
    RelCT isa (Eq2 σ₁ σ₂) (VG.Impl.AesGcm.AArch64.tag v.callees o) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (tagSeg o)) h).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have k₁22 : k₁ .x22 = BitVec.ofNat 64 R := (hk₁ .x22 (by decide)).symm.trans h22₁
  have k₂22 : k₂ .x22 = BitVec.ofNat 64 R := (hk₂ .x22 (by decide)).symm.trans h22₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.lens_rel L v (.inr rfl) (by decide) he₁ he₂ hk₁ hk₂ h25₁ h25₂ ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.lens_ok L v (.inr rfl) (by decide) he₁ hk₁ h25₁) (VG.Proof.AesGcm.AArch64.lens_ok L v (.inr rfl) (by decide) he₂ hk₂ h25₂)
    fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [a₁.env.sp, a₂.env.sp])
      (by agree_tac [a₁.env.x19, a₂.env.x19, a₁.env.x20, a₂.env.x20, a₁.env.x21, a₂.env.x21]) t₁)
    (tagSeg_ok L ho a₁.env a₁.kept ((a₁.kept .x22 (by decide)).trans k₁22) hR)
    (tagSeg_ok L ho a₂.env a₂.kept ((a₂.kept .x22 (by decide)).trans k₂22) hR) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_ctr v.ctr b₁.call b₂.call (by rw [b₁.env.sp, b₂.env.sp])

/-- `j0hash`. -/
theorem j0hash_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0hash v.callees) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (j0Seg_ok L h₁) (j0Seg_ok L h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (j0Call1_ok L v a₁) (j0Call1_ok L v a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  have hlt := h₁.data.lt
  have pad : ∀ {k : Reg → BitVec 64} {H : Block} {m₀ : Mem} {σ : State}, J2 Ctx St W SP k H Np n m₀ σ →
      WP isa (padSeg 0 [mov .x12 .x23]) σ (Pad1 Ctx St W SP k 0 (n % 16) (Np + BitVec.ofNat 64 (16 * (n / 16)))
        σ.mem) := fun b => by
    have hdr := b.data.drop (k := 16 * (n / 16)) (by omega)
    rw [show n - 16 * (n / 16) = n % 16 by omega] at hdr
    exact padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
      b.env b.kept b.x25 (Nat.mod_lt _ (by decide))
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, b.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x25] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x25, b₂.x25]) ⟨_, by taint_decide⟩)
    (pad b₁) (pad b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (padCall_ok L (.inl rfl) v c₁) (padCall_ok L (.inl rfl) v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact VG.Proof.AesGcm.AArch64.lens_rel L v (.inl rfl) (by decide) d₁.env d₂.env d₁.kept d₂.kept d₁.x25 d₂.x25 ⟨_, by taint_decide⟩

omit L in
/-- The test of the nonce's length. -/
theorem j0pre_ok {s : State} {n : Nat} (h24 : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x9 .x24 12]) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ Regs [.x9] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem J0In.of_regs {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s s' : State}
    (h : J0In Ctx St W SP k H Np n s) (r : Regs [.x9] s s') : J0In Ctx St W SP k H Np n s' :=
  ⟨h.env.of_regs r, h.kept.of_others r.others, by rw [r.others _ (by decide)]; exact h.x23,
    by rw [r.others _ (by decide)]; exact h.x24, by rw [r.others _ (by decide)]; exact h.x26,
    by rw [r.others _ (by decide)]; exact h.x27, h.data.of_eq r.rd r.wr, by rw [r.mem]; exact h.hH⟩

omit L in
theorem j0ev {s : State} {n : Nat} (hlt : n < 2 ^ 64) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    isa.eval (.zero .x .x9) s = some (decide (n = 12)) := by
  show some (s.read .x .x9 == 0) = _
  rw [State.read, h9, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]

/-- The branch of `j0`, run. -/
theorem j0ite_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    WP isa (.ite (.zero .x .x9) (.block j012) (j0hash v.callees)) s
      (J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  refine WP.ite (decide (n = 12)) (VG.Proof.AesGcm.AArch64.j0ev h.data.lt h9) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact j012_ok L h
  · exact j0hash_ok L v h (by simpa using hf)

/-- `j0`. -/
theorem j0_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0 v.callees) TT := by
  refine rel_seq (rel_taint [.x24] (by rw [h₁.env.sp, h₂.env.sp]) (by agree_tac [h₁.x24, h₂.x24])
      ⟨_, by taint_decide⟩) (VG.Proof.AesGcm.AArch64.j0pre_ok h₁.x24) (VG.Proof.AesGcm.AArch64.j0pre_ok h₂.x24) fun τ₁ τ₂ ⟨a₁, r₁⟩ ⟨a₂, r₂⟩ => ?_
  have g₁ := h₁.of_regs r₁
  have g₂ := h₂.of_regs r₂
  refine rel_seq (rel_ite (VG.Proof.AesGcm.AArch64.j0ev h₁.data.lt a₁) (VG.Proof.AesGcm.AArch64.j0ev h₁.data.lt a₂) (fun ht => ?_) (fun _ => ?_))
    (VG.Proof.AesGcm.AArch64.j0ite_ok L v g₁ a₁) (VG.Proof.AesGcm.AArch64.j0ite_ok L v g₂ a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  · have h12 : n = 12 := by simpa using ht
    exact rel_taint [.x20, .x23] (by rw [g₁.env.sp, g₂.env.sp])
      (by agree_tac [g₁.env.x20, g₂.env.x20, g₁.x23, g₂.x23]) ⟨_, by taint_decide⟩
  · exact VG.Proof.AesGcm.AArch64.j0hash_rel L v g₁ g₂
  · exact rel_taint [.x20] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x20, b₂.env.x20])
      ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT`. -/
section

/-!
# AES-GCM on AArch64: the bodies are constant time

Untrusted: everything here is checked by Lean. Two runs of `encBody`,
`decAbs`, `decBody` or `finBody` from states with the same public values (the
lengths and the offset of the buffered additional data) leak the same.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

omit L in
theorem hz_mod (o : Nat) (ho : o < 16) : (Spec.Gcm.zeros o).length % 16 = o := by
  rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt ho

/-- `fo`, `flush` and `textArgs` in two runs, and what each leaves. -/
theorem padArgs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, CrIn Ctx St W SP k₁ R P D n τ₁ → CrIn Ctx St W SP k₂ R P D n τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq fo (.seq (flush v.callees 16) (.seq (.block textArgs) rest))) TT := by
  have hn := h₁.data.ok.lt
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k27₁ : k₁ .x27 = BitVec.ofNat 64 P := (h₁.kept .x27 (by decide)).symm.trans h₁.x27
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (h₁.kept .x22 (by decide)).symm.trans h₁.x22
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k27₂ : k₂ .x27 = BitVec.ofNat 64 P := (h₂.kept .x27 (by decide)).symm.trans h₂.x27
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (h₂.kept .x22 (by decide)).symm.trans h₂.x22
  refine rel_seq (rel_taint [.x25, .x26, .x27] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.x25, h₂.x25, hq, h₁.x26, h₂.x26, h₁.x27, h₂.x27]) ⟨_, by taint_decide⟩)
    (fo_ok h₁.x25 h₁.x26 h₁.x27 hn h₁.hP) (fo_ok h₂.x25 h₂.x26 h₂.x27 hn h₂.hP)
    fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have he₁ := h₁.env.of_regs r₁
  have he₂ := h₂.env.of_regs r₂
  have hk₁ := h₁.kept.of_others r₁.others
  have hk₂ := h₂.kept.of_others r₂.others
  rw [← hq] at x25₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.flush_rel L v (.inr rfl) he₁ he₂ hk₁ hk₂ x25₁ x25₂ (by split <;> omega))
    (WP.with_rdwr (flushStep_ok L v (a := a₁) (c := c₁) (n := n) he₁ hk₁ (by rw [x25₁, h₁.hc]) rfl))
    (WP.with_rdwr (flushStep_ok L v (a := a₂) (c := c₂) (n := n) he₂ hk₂ (by rw [x25₂, h₂.hc, hq]) rfl))
    fun τ₁ τ₂ ⟨⟨fe₁, fk₁, _, _, _⟩, frd₁, fwr₁⟩ ⟨⟨fe₂, fk₂, _, _, _⟩, frd₂, fwr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x27, .x28] (by rw [fe₁.sp, fe₂.sp])
      (by agree_tac [fk₁ .x26 (by decide), fk₂ .x26 (by decide), fk₁ .x27 (by decide), fk₂ .x27 (by decide),
        fk₁ .x28 (by decide), fk₂ .x28 (by decide), k26₁, k26₂, k27₁, k27₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textArgs_ok fk₁ k26₁ k27₁ k28₁ h₁.hP) (textArgs_ok fk₂ k26₂ k27₂ k28₂ h₂.hP)
    fun τ₁ τ₂ ⟨a25₁, a23₁, a24₁, ra₁⟩ ⟨a25₂, a23₂, a24₂, ra₂⟩ => ?_
  have ge₁ := fe₁.of_regs ra₁
  have ge₂ := fe₂.of_regs ra₂
  have gk₁ := fk₁.of_others ra₁.others
  have gk₂ := fk₂.of_others ra₂.others
  exact hr τ₁ τ₂
    ⟨ge₁, gk₁, (gk₁ .x22 (by decide)).trans k22₁, h₁.rounds, a23₁, a24₁, a25₁,
      h₁.data.of_eq (by rw [ra₁.rd, frd₁, r₁.rd]) (by rw [ra₁.wr, fwr₁, r₁.wr])⟩
    ⟨ge₂, gk₂, (gk₂ .x22 (by decide)).trans k22₂, h₂.rounds, a23₂, a24₂, a25₂,
      h₂.data.of_eq (by rw [ra₂.rd, frd₂, r₂.rd]) (by rw [ra₂.wr, fwr₂, r₂.wr])⟩

/-- `textAbs` in two runs. -/
theorem textAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {σ₁ σ₂ : State}
    (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h23₁ : σ₁.gpr .x23 = D) (h23₂ : σ₂.gpr .x23 = D)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 n) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 n)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (P % 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (P % 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 n) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 n)
    (hd₁ : DataOk St W σ₁ D n) (hd₂ : DataOk St W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (textAbs v.callees) TT := by
  refine rel_ite (eval_zero h26₁ hd₁.lt) (eval_zero h26₂ hd₁.lt) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [he₁.sp, he₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact VG.Proof.AesGcm.AArch64.absorb_rel L v (.inr rfl)
      (⟨he₁, hk₁, h23₁, h24₁, h25₁, VG.Proof.AesGcm.AArch64.hz_mod _ (Nat.mod_lt _ (by decide)), hd₁, rfl⟩ :
        AbsIn Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₁)
      (⟨he₂, hk₂, h23₂, h24₂, h25₂, VG.Proof.AesGcm.AArch64.hz_mod _ (Nat.mod_lt _ (by decide)), hd₂, rfl⟩ :
        AbsIn Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₂)

/-- `encBody` in two runs. -/
theorem encBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (encBody v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine VG.Proof.AesGcm.AArch64.padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (VG.Proof.AesGcm.AArch64.crypt_rel L v c₁ c₂) (WP.with_rdwr (crypt_ok L v (icb := 0) c₁))
    (WP.with_rdwr (crypt_ok L v (icb := 0) c₂)) fun τ₁' τ₂' ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [o₁.kept .x26 (by decide), o₂.kept .x26 (by decide), o₁.kept .x28 (by decide),
        o₂.kept .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok o₁.kept k26₁ k28₁) (textPiece_ok o₂.kept k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := o₁.kept.of_others rp₁.others
  have pk₂ := o₂.kept.of_others rp₂.others
  exact VG.Proof.AesGcm.AArch64.textAbs_rel L v (o₁.env.of_regs rp₁) (o₂.env.of_regs rp₂) pk₁ pk₂ p23₁ p23₂ p24₁ p24₂
    (by rw [rp₁.others _ (by decide), o₁.x25]) (by rw [rp₂.others _ (by decide), o₂.x25])
    ((pk₁ .x26 (by decide)).trans k26₁) ((pk₂ .x26 (by decide)).trans k26₂)
    (c₁.data.ok.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁]))
    (c₂.data.ok.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂]))

/-- `finBody o` in two runs. -/
theorem finBody_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {R A P : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h22₁ : σ₁.gpr .x22 = BitVec.ofNat 64 R) (h22₂ : σ₂.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 A) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 A)
    (h27₁ : σ₁.gpr .x27 = BitVec.ofNat 64 P) (h27₂ : σ₂.gpr .x27 = BitVec.ofNat 64 P)
    (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (finBody v.callees o) TT := by
  have ho' : (if P = 0 then A % 16 else P % 16) < 16 := by split <;> exact Nat.mod_lt _ (by decide)
  refine rel_seq (rel_taint [.x26, .x27] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [h26₁, h26₂, h27₁, h27₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.finOff_ok h26₁ h27₁ hA hP) (VG.Proof.AesGcm.AArch64.finOff_ok h26₂ h27₂ hA hP) fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have fe₁ := he₁.of_regs r₁
  have fe₂ := he₂.of_regs r₂
  have fk₁ := hk₁.of_others r₁.others
  have fk₂ := hk₂.of_others r₂.others
  refine rel_seq (VG.Proof.AesGcm.AArch64.flush_rel L v (.inr rfl) fe₁ fe₂ fk₁ fk₂ x25₁ x25₂ ho')
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₁.mem (Ctx + BitVec.ofNat 64 240)) fe₁ fk₁
      x25₁ (VG.Proof.AesGcm.AArch64.hz_mod _ ho') rfl)
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₂.mem (Ctx + BitVec.ofNat 64 240)) fe₂ fk₂
      x25₂ (VG.Proof.AesGcm.AArch64.hz_mod _ ho') rfl) fun τ₁ τ₂ ⟨t₁, _, _⟩ ⟨t₂, _, _⟩ => ?_
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (hk₁ .x22 (by decide)).symm.trans h22₁
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (hk₂ .x22 (by decide)).symm.trans h22₂
  exact VG.Proof.AesGcm.AArch64.tag_rel L v ho t₁.env t₂.env t₁.kept t₂.kept ((t₁.kept .x22 (by decide)).trans k22₁)
    ((t₂.kept .x22 (by decide)).trans k22₂) hR t₁.x25 t₂.x25

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `j0`'s arguments (`siEntry_ok`); `j0` writes `J₀`, a
zero accumulator and the first counter block, which is a state for the
nonce, no additional data and no text.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)

theorem covers_mem {r : Region} {rd wr : List Region} (h : r ∈ rd ++ wr) : Covers [r] (rd ++ wr) :=
  covers_of_mem h

/-- After the entry: `j0`'s arguments. -/
theorem siEntry_ok {s : State} {Ctx Np St W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hNp : s.gpr .x1 = Np)
    (hn : (s.gpr .x2).toNat = n) (hSt : s.gpr .x3 = St) (hW : s.gpr .x4 = W)
    (hperm : Perm Ctx St W s) :
    WP isa (.block siEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x23 = Np ∧ s'.gpr .x24 = BitVec.ofNat 64 n ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧
      s'.gpr .x27 = 0 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x4 hW hperm.w
  have hn' : s.gpr .x2 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x26₂, x27₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x4, mov .x20 .x3, mov .x21 .x0, mov .x23 .x1, mov .x24 .x2, mov .x26 .x2, imm .x27 0] s₁ =
        some s₂ ∧ s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x23 = Np ∧
      s₂.gpr .x24 = BitVec.ofNat 64 n ∧ s₂.gpr .x26 = BitVec.ofNat 64 n ∧ s₂.gpr .x27 = 0 ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hCtx, hNp, hn', hSt, hW]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x23₂, x24₂, x26₂, x27₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem streamInit_wp (v : GcmImpl) {s : State} (hs : streamInitAArch64.pre s) :
    WP isa (streamInit v.callees) s fun s' => GprAbi s s' ∧ streamInitAArch64.post s s' := by
  simp only [streamInitAArch64] at hs ⊢
  obtain ⟨hrd, hwr, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hNp : s.gpr .x1 = Np at *
  generalize hn : (s.gpr .x2).toNat = n at *
  generalize hSt : s.gpr .x3 = St at *
  generalize hW : s.gpr .x4 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x2).isLt
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.siEntry_ok hCtx hNp hn hSt hW perm)
    fun s₁ ⟨he₁, hk₁, x23₁, x24₁, x26₁, x27₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n :=
    bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have hJ : J0In Ctx St W s.sp s₁.gpr (Spec.Gcm.ctxH s.mem Ctx) Np n s₁ :=
    ⟨he₁, hk₁, x23₁, x24₁, x26₁, x27₁,
      ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [rd₁, wr₁, hrd]; simp), hlt, wn, dns, dnw⟩, hH⟩
  refine WP.seq (WP.mono (j0_ok L v hJ) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame (saved_j0Frame L)
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ciph => ?_⟩
  rw [hm, hiv] at *
  refine Proof.Gcm.streamRepr_iff.mpr ⟨h₂.j0, Proof.Gcm.absorbed_nil _ h₂.y, Proof.Gcm.ctr_zero _ _ _ _ h₂.cb⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamAad`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments, with `aad_len mod 16` bytes
buffered (`aadEntry_ok`); `absorb` takes the data into GHASH and touches
nothing else of the state (`aad_run`), for any additional data so far of
that length (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- After the entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hD : s.gpr .x3 = D) (hn : (s.gpr .x4).toNat = n) (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block aadEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x23 = D ∧ s'.gpr .x24 = BitVec.ofNat 64 n ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x5 hW hperm.w
  have hn' : s.gpr .x4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x5, mov .x20 .x1, mov .x21 .x0, mov .x23 .x3, mov .x24 .x4, imm .x9 15,
        .logic .and .x .x25 .x2 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x23 = D ∧
      s₂.gpr .x24 = BitVec.ofNat 64 n ∧ s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hD]
    · simp [gpr_write, g₁, hn']
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x23₂, x24₂, x25₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W : Addr) : List Region := savedR W :: absFrame St W 16

/-- One run of `stream_aad`, for additional data `x` so far of `o` bytes modulo 16. -/
theorem aad_run (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .x2).toNat % 16) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) x →
        Absorbed s'.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (x ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ∧
      Frame (VG.Proof.AesGcm.AArch64.aadFrame (s.gpr .x1) (s.gpr .x5)) s.mem s'.mem := by
  simp only [streamAadAArch64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x1 = St at *
  generalize hD : s.gpr .x3 = D at *
  generalize hn : (s.gpr .x4).toNat = n at *
  generalize hW : s.gpr .x5 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x4).isLt
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.aadEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x23₁, x24₁, x25₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have dS : ∀ (d k : Nat), d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR W) :=
    fun d k h => L.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR W] s.mem m →
      Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x →
      Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (Spec.Gcm.ctxH s.mem Ctx) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega))
  have hIn : AbsIn Ctx St W s.sp s₁.gpr (Spec.Gcm.ctxH s.mem Ctx) x D n ((s.gpr .x2).toNat % 16) s₁ :=
    ⟨he₁, hk₁, x23₁, x24₁, x25₁, hx, ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [rd₁, wr₁, hrd]; simp), hlt, wd, dds, ddw⟩, hH⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) v hIn) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame (saved_absFrame L (.inr rfl))
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_, ?_⟩
  · rw [hm, ← hdat]; exact h₂.abs (hA _ fsv ha)
  · rw [hm]
    exact (fsv.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (h₂.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp (v : GcmImpl) {s : State} (hs : streamAadAArch64.pre s) :
    WP isa (streamAad v.callees) s fun s' => GprAbi s s' ∧ streamAadAArch64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .x2).toNat % 16)).length % 16 = (s.gpr .x2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1 i.2.2 [] ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .x1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .x0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) [])
    (VG.Proof.AesGcm.AArch64.aad_run v hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .x2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadAArch64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww⟩ := hs'
  have dSt : ∀ r ∈ VG.Proof.AesGcm.AArch64.aadFrame (s.gpr .x1) (s.gpr .x5), ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .x1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .x1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega) (by omega)
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide))
    · exact st_off 16 16 (by decide) (by omega)
    · exact st_off 32 16 (by decide) (by omega)
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide))
  refine WP.mono (VG.Proof.AesGcm.AArch64.aad_run v hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamCrypt`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up the body's arguments (`crEntry_ok`); the body
encrypts (`encBody_ok`) or decrypts (`decBody_ok`) and absorbs the
ciphertext, for any message so far of those lengths (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput StreamRepr gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry: the body's arguments. -/
theorem crEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hD : s.gpr .x5 = D) (hn : (s.gpr .x6).toNat = n) (hW : s.gpr .x7 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block crEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x3).toNat % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧
      s'.gpr .x27 = BitVec.ofNat 64 (s.gpr .x4).toNat ∧ s'.gpr .x28 = D ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x7 hW hperm.w
  have hn' : s.gpr .x6 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x26₂, x27₂, x28₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x7, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x6, mov .x27 .x4, mov .x28 .x5,
        imm .x9 15, .logic .and .x .x25 .x3 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s₂.gpr .x26 = BitVec.ofNat 64 n ∧
      s₂.gpr .x27 = BitVec.ofNat 64 (s.gpr .x4).toNat ∧ s₂.gpr .x28 = D ∧
      s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x3).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁]
    · simp [gpr_write, g₁, hn']
    · simp [gpr_write, g₁]
    · simp [gpr_write, g₁, hD]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x22₂, x25₂, x26₂, x27₂, x28₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What a run of `encrypt` or `decrypt` leaves, for the message `a`, `c` so far. -/
def CrRun (s : State) (a c : List Byte) (icb : Block) (e out : List Byte) (s' : State) : Prop :=
  GprAbi s s' ∧
  Frame (savedR (s.gpr .x7) :: bodyFrame (s.gpr .x2) (s.gpr .x7) (s.gpr .x5) (s.gpr .x6).toNat) s.mem s'.mem ∧
  (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
    Ctr s.mem (s.gpr .x2 + BitVec.ofNat 64 48) (s.gpr .x2 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat →
    Absorbed s'.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a (c ++ e)) ∧
    Ctr s'.mem (s.gpr .x2 + BitVec.ofNat 64 48) (s.gpr .x2 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb ((s.gpr .x4).toNat + (s.gpr .x6).toNat) ∧
    bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = out)

/-- The entry, `body`, and the exit: what `body` does, moved to the entry
state. -/
theorem cr_run {body : Prog isa} {s : State} (hs : streamCryptPre s) {a c : List Byte}
    (ha : a.length % 16 = (s.gpr .x3).toNat % 16) (hc : c.length = (s.gpr .x4).toNat) {icb : Block}
    {E O : Mem → List Byte}
    (hE : ∀ m, Frame [savedR (s.gpr .x7)] s.mem m → E m = E s.mem)
    (hO : ∀ m, Frame [savedR (s.gpr .x7)] s.mem m → O m = O s.mem)
    (hb : ∀ {k : Reg → BitVec 64} {s₁ : State}, Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) →
      BodyIn (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp k (s.gpr .x1).toNat (s.gpr .x6).toNat (s.gpr .x4).toNat
        (s.gpr .x5) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) s₁ →
      WP isa body s₁ (BodyOut (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp k (s.gpr .x1).toNat (s.gpr .x6).toNat
        (s.gpr .x4).toNat (s.gpr .x5) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) icb (E s₁.mem) (O s₁.mem) s₁.mem)) :
    WP isa (.seq (.block crEntry) (.seq body (.block restore))) s (VG.Proof.AesGcm.AArch64.CrRun s a c icb (E s.mem) (O s.mem)) := by
  unfold VG.Proof.AesGcm.AArch64.CrRun
  simp only [streamCryptPre] at hs
  obtain ⟨hrd, hwr, dcs, dcd, dcw, dsd, dsw, ddw, wc, ws, wd, ww, hR⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x2 = St at *
  generalize hD : s.gpr .x5 = D at *
  generalize hn : (s.gpr .x6).toNat = n at *
  generalize hW : s.gpr .x7 = W at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hP : (s.gpr .x4).toNat = P at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x6).isLt
  have hPlt : P < 2 ^ 64 := hP ▸ (s.gpr .x4).isLt
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.crEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x25₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hRR] at x22₁
  rw [hP] at x27₁
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have hdat : DataW Ctx St W s₁ D n :=
    ⟨⟨covers_left (by rw [wr₁, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
      by rw [wr₁, hwr]; exact covers_of_mem (by simp), dcd⟩
  have hIn : BodyIn Ctx St W s.sp s₁.gpr R n P D a c (Spec.Gcm.ctxH s.mem Ctx) s₁ :=
    ⟨he₁, hk₁, x22₁, hRR ▸ hR, by rw [x25₁, ha], x26₁, x27₁, x28₁, hc, hPlt, hdat, hH⟩
  refine WP.seq (WP.mono (hb L hIn) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact saved_tFrame L (.inr rfl) r hr
        · exact saved_crFrame L hdat r hr
      · exact saved_absFrame L (.inr rfl) r hr
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, ?_, fun habs hctr => ?_⟩
  · rw [hm]
    exact (fsv.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (h₂.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · have hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R :=
      ciph_frame fsv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW) (hRR ▸ hR)
    have hA₁ := Absorbed.frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩) habs
    have hC₁ := Ctr.frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩) hctr
    rw [← hc₁] at hC₁
    obtain ⟨o₁, o₂, o₃⟩ := h₂.post hA₁ hC₁
    rw [hc₁] at o₂
    rw [hE _ fsv] at o₁
    rw [hO _ fsv] at o₃
    rw [hm]
    exact ⟨o₁, o₂, o₃⟩

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput StreamRepr gctr inc32 ctxCiph ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- `J₀` is apart from what a run of `encrypt` or `decrypt` writes. -/
theorem st0_crRun {Ctx St W D : Addr} {n : Nat} (L : Lay Ctx St W) (hd : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ savedR W :: bodyFrame St W D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with h | hr
  · subst h; exact st0_saved L
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Region.sub_prefix (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

/-- What does not change in the entry's writes. -/
theorem crypt_inv {s : State} (hs : streamCryptPre s) {m : Mem} (hf : Frame [savedR (s.gpr .x7)] s.mem m) :
    ciphOf m (s.gpr .x0) (s.gpr .x1).toNat = ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat ∧
      bytesAt m (s.gpr .x5) (s.gpr .x6).toNat = bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat := by
  simp only [streamCryptPre] at hs
  obtain ⟨-, -, -, -, dcw, -, -, ddw, -, -, -, -, hR⟩ := hs
  have sW : Region.Sub (savedR (s.gpr .x7)) ⟨s.gpr .x7, 2560⟩ := Lay.wSub (by decide)
  exact ⟨ciph_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW) hR,
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega)⟩

theorem lay_of_crypt {s : State} (hs : streamCryptPre s) : Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) ∧
    (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 80⟩ := by
  simp only [streamCryptPre] at hs
  obtain ⟨-, -, dcs, -, dcw, dsd, dsw, -, wc, ws, -, ww, -⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw, dsd.symm⟩

theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hs : streamEncryptAArch64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => GprAbi s s' ∧ streamEncryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x3).toNat % 16 →
      c.length = (s.gpr .x4).toNat → WP isa (streamEncrypt v.callees) s (VG.Proof.AesGcm.AArch64.CrRun s a c icb
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))) := fun a c icb ha hc =>
    VG.Proof.AesGcm.AArch64.cr_run (E := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat))
      (O := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)) hs' ha hc
      (fun m hf => by simp only [(VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).1, (VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).2])
      (fun m hf => by simp only [(VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).1, (VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).2])
      (fun L h => encBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x3).toNat % 16)).length % 16 = (s.gpr .x3).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length = (s.gpr .x4).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := VG.Proof.AesGcm.AArch64.lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) i.2.2) ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x2) ciph h i.1 i.2.1
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)) ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, p⟩ ⟨hr, hl, hp⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a p hr hl hp => hq ⟨iv, a, p⟩ ⟨hr, hl, hp⟩⟩
  have hp : (s.gpr .x4).toNat = p.length := hp
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x3).toNat % 16 := by rw [hl, toNat_mod16]
  have hlen : (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p).length = (s.gpr .x4).toNat := by
    rw [Proof.Gcm.length_gctr, hp]
  refine WP.mono (run a _ (inc32 (Spec.Gcm.j0 h iv)) ha hlen) fun s' ⟨_, hf, hpost⟩ => ?_
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [hlen] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  have he : gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) =
      gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p ++ xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (inc32 (Spec.Gcm.j0 h iv)) (s.gpr .x4).toNat (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) := by
    rw [Proof.Gcm.gctr_append, hp]; rfl
  show StreamRepr s'.mem (s.gpr .x2) ciph h iv a _ ∧ _
  rw [he]
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (VG.Proof.AesGcm.AArch64.st0_crRun L hds)
  · rw [List.length_append, hlen, Proof.Gcm.length_xorKs, length_bytesAt]; exact o₂
  · rw [List.drop_left' (by rw [hlen, hp]), o₃]

theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hs : streamDecryptAArch64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => GprAbi s s' ∧ streamDecryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x3).toNat % 16 →
      c.length = (s.gpr .x4).toNat → WP isa (streamDecrypt v.callees) s (VG.Proof.AesGcm.AArch64.CrRun s a c icb
        (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))) := fun a c icb ha hc =>
    VG.Proof.AesGcm.AArch64.cr_run (E := fun m => bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)
      (O := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)) hs' ha hc
      (fun m hf => by simp only [(VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).2])
      (fun m hf => by simp only [(VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).1, (VG.Proof.AesGcm.AArch64.crypt_inv hs' hf).2])
      (fun L h => decBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x3).toNat % 16)).length % 16 = (s.gpr .x3).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length = (s.gpr .x4).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := VG.Proof.AesGcm.AArch64.lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x2) ciph h i.1 i.2.1 (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x3).toNat % 16 := by rw [hl, toNat_mod16]
  refine WP.mono (run a c (inc32 (Spec.Gcm.j0 h iv)) ha hc.symm) fun s' ⟨_, hf, hpost⟩ => ?_
  show StreamRepr s'.mem (s.gpr .x2) ciph h iv a _ ∧ _
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [← hc] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (VG.Proof.AesGcm.AArch64.st0_crRun L hds)
  · rw [List.length_append, ← hc, length_bytesAt]; exact o₂
  · rw [Proof.Gcm.gctr_append, List.drop_left' (by rw [Proof.Gcm.length_gctr]), o₃, hc]; rfl

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers, keeps the lengths in `x26` and `x27` (`finEntry_ok`) and `tag`
in `x28` (`finishEntry_ok`); `finBody 0` writes the tag to `W`, for any
message of those lengths (`WP.forall_det`), and `tagOut` copies it to
`tag`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- After the entry, with `work` in `w`: the lengths. -/
theorem finEntry_ok {s : State} {Ctx St W : Addr} {w : Reg} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr w = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry w)) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = s.gpr .x4 ∧
      s'.gpr .x5 = s.gpr .x5 ∧ s'.gpr .x6 = s.gpr .x6 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s w hW hperm.w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x26₂, x27₂, x5₂, x6₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 w, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x3, mov .x27 .x4] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s₂.gpr .x26 = s.gpr .x3 ∧ s₂.gpr .x27 = s.gpr .x4 ∧
      s₂.gpr .x5 = s.gpr .x5 ∧ s₂.gpr .x6 = s.gpr .x6 ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hW, hSt, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x22₂, x26₂, x27₂, x5₂, x6₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The entry of `finish`: `tag` in `x28`. -/
theorem finishEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr .x6 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x6 ++ [mov .x28 .x5])) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = s.gpr .x4 ∧
      s'.gpr .x28 = s.gpr .x5 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.AArch64.finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x22₁, x26₁, x27₁, x5₁, _, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  have r : Regs [.x28] s₁ (s₁.write .x .x28 (s₁.gpr .x5 + BitVec.ofNat 64 0)) :=
    ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  exact ⟨he₁.of_regs r, fun _ _ => rfl, by rw [r.others _ (by decide), x22₁],
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by simp [gpr_write, x5₁],
    by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `finPre` gives. -/
theorem lay_of_fin {s : State} (hs : finPre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) ∧ Perm (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) s ∧
      rounds (s.gpr .x1) ∧ Covers [⟨s.gpr .x5, 16⟩] s.wr ∧
      (⟨s.gpr .x5, 16⟩ : Region).Disjoint ⟨s.gpr .x6, 2560⟩ := by
  simp only [finPre] at hs
  obtain ⟨hrd, hwr, dcs, -, dcw, -, dsw, dtw, wc, ws, -, ww, hR⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw,
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩, hR,
    covers_of_mem (by rw [hwr]; simp), dtw⟩

/-- What writes to the parts `rs` of `W` keep, outside the state. -/
theorem fin_inv {Ctx St W : Addr} (L : Lay Ctx St W) {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩) {m₀ m : Mem} (hf : Frame rs m₀ m)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {x : List Byte} :
    ciphOf m Ctx R = ciphOf m₀ Ctx R ∧ blockAt m St = blockAt m₀ St ∧
      blockAt m (Ctx + BitVec.ofNat 64 240) = ctxH m₀ Ctx ∧
      (Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x →
        Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x) :=
  ⟨ciph_frame hf (fun r hr => L.cw'.sub_right (hrs r hr).2) hR,
    blockAt_frame hf (fun r hr => (hrs r hr).1.sub_left (Region.sub_prefix (by decide))),
    blockAt_frame hf (fun r hr => (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (hrs r hr).2),
    fun ha => Absorbed.frame hf (fun r hr => (hrs r hr).1.sub_left (Lay.stSub (by decide))) ha⟩

/-- The saved registers' slots are parts of `W` outside the state. -/
theorem savedR_inv {Ctx St W : Addr} (L : Lay Ctx St W) :
    ∀ r ∈ [savedR W], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩ := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.sb.sub_right (Lay.bSub (by decide) (by decide)), Lay.wSub (by decide)⟩

/-- One run of `stream_finish`, for a message `a`, `c` of those lengths. -/
theorem fin_run (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        bytesAt s'.mem (s.gpr .x5) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, hR, tW, dtw⟩ := VG.Proof.AesGcm.AArch64.lay_of_fin hs'
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finishEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR (s.gpr .x6)] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := VG.Proof.AesGcm.AArch64.fin_inv L (VG.Proof.AesGcm.AArch64.savedR_inv L) fsv hR (x := ghashInput a c)
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.finBody_ok L v (.inl rfl) (a := a) (c := c) he₁ hk₁ x22₁ hR
    (by rw [x26₁, h3]) (by rw [x27₁, h4]) hc hH₁)) fun s₂ ⟨⟨he₂, hk₂, f₂, out₂⟩, _, wr₂⟩ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .x6) s := by
    have := savedAt_save s.mem (s.gpr .x6) s
    rw [← m₁] at this
    exact this.frame f₂ (VG.Proof.AesGcm.AArch64.saved_finFrame L (.inl rfl))
  have x28₂ : s₂.gpr .x28 = s.gpr .x5 := by rw [hk₂ .x28 (by decide), x28₁]
  refine WP.seq (WP.mono (tagOut_ok he₂.x19 x28₂ (covers_left he₂.perm.w) (by rw [wr₂, wr₁]; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₃ ⟨out₃, f₃, og₃, sp₃, rd₃, wr₃⟩ => ?_)
  have he₃ : Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) s.sp s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have hsv₃ : SavedAt s₃.mem (s.gpr .x6) s := hsv.frame f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₃.x19 he₃.sp (covers_left he₃.perm.w) hsv₃) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hm, out₃, ← hc₁, ← hj₁]
  have := out₂ (hA₁ ha)
  rw [add_ofNat_zero] at this
  exact this

theorem streamFinish_wp (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧ streamFinishAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' => bytesAt s'.mem (s.gpr .x5) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2)
    (VG.Proof.AesGcm.AArch64.fin_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (VG.Proof.AesGcm.AArch64.fin_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  show _ = Spec.Gcm.fullTag ciph h iv a c
  rw [hout habs, Proof.Gcm.fullTag_eq, hj]
  rfl

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. After the entry, `tagLenOk`
checks the tag length (a public value); if §5.2.1.2 does not allow it, 0 is
returned; otherwise `tagIn` copies the received tag to `W`, `finBody 112`
writes the tag at `W + 112`, `cmpSeg` compares its first `tag_len` bytes with
the received ones without a branch, and `verRet` returns 1 or 0
(`ver_run`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH zeros)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem tagLenOk_le {t : Nat} (h : Spec.Gcm.tagLenOk t = true) : t ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem setWidth_ofNat_bool (b : Bool) :
    (BitVec.ofNat 64 (if b then 1 else 0)).setWidth 32 = if b then 1 else 0 := by
  cases b <;> rfl

/-- The entry of `verify`: `tag_len` in `x28` and `tag` in `x12`. -/
theorem verEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr .x7 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x7 ++ [mov .x28 .x6, mov .x12 .x5])) s fun s' => Env Ctx St W s.sp s' ∧
      Kept s'.gpr s' ∧ s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧
      s'.gpr .x27 = s.gpr .x4 ∧ s'.gpr .x28 = s.gpr .x6 ∧ s'.gpr .x12 = s.gpr .x5 ∧
      s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.AArch64.finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x22₁, x26₁, x27₁, x5₁, x6₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  have r : Regs [.x28, .x12] s₁ s' := by subst hs'; exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  have x28' : s'.gpr .x28 = s₁.gpr .x6 := by subst hs'; simp [gpr_write]
  have x12' : s'.gpr .x12 = s₁.gpr .x5 := by subst hs'; simp [gpr_write]
  exact ⟨he₁.of_regs r, fun _ _ => rfl, by rw [r.others _ (by decide), x22₁],
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by rw [x28', x6₁],
    by rw [x12', x5₁], by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `verPre` gives. -/
theorem lay_of_ver {s : State} (hs : verPre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) ∧ Perm (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s ∧
      rounds (s.gpr .x1) ∧ Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 2560⟩ := by
  simp only [verPre] at hs
  obtain ⟨hrd, hwr, dcs, dcw, -, dsw, dtw, wc, ws, -, ww, hR⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw,
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩, hR,
    VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- The parts of `W` that the entry and `tagIn` write. -/
theorem tag16_inv {Ctx St W : Addr} (L : Lay Ctx St W) :
    ∀ r ∈ [savedR W, ⟨W, 16⟩], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.AesGcm.AArch64.savedR_inv L _ (List.mem_singleton_self _)
  · exact ⟨L.sa, Region.sub_prefix (by decide)⟩

/-- One run of `stream_verify`, for a message `a`, `c` of those lengths. -/
theorem ver_run (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        let T := toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))
        if Spec.Gcm.tagLenOk (s.gpr .x6).toNat ∧ T.take (s.gpr .x6).toNat =
            bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat then (s'.gpr .x0).setWidth 32 = 1
        else (s'.gpr .x0).setWidth 32 = 0) := by
  have hs' : verPre s := hs
  obtain ⟨L, perm, hR, tR, dtw⟩ := VG.Proof.AesGcm.AArch64.lay_of_ver hs'
  generalize hT : toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
      [ofBytes (lensBlock a.length c.length)] ^^^
      ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) = T
  generalize htl : (s.gpr .x6).toNat = tl at tR dtw ⊢
  have htl' : tl < 2 ^ 64 := htl ▸ (s.gpr .x6).isLt
  -- The entry.
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.verEntry_ok rfl rfl rfl perm)
    fun s₂ ⟨he₂, hk₂, x22₂, x26₂, x27₂, x28₂, x12₂, m₂, rd₂, wr₂⟩ => ?_)
  have x28₂' : s₂.gpr .x28 = BitVec.ofNat 64 tl := by rw [x28₂, ← htl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have fsv : Frame [savedR (s.gpr .x7)] s.mem s₂.mem := by rw [m₂]; exact savedMem_frame _ _ _
  refine WP.seq (WP.mono (tagLenOk_ok s₂ x28₂' htl') fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have sv₃ : SavedAt s₃.mem (s.gpr .x7) s := by
    have := savedAt_save s.mem (s.gpr .x7) s
    rwa [← m₂, ← m₃] at this
  have ev : isa.eval (.zero .x .x9) s₃ =
      some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp s₄ ∧
      SavedAt s₄.mem (s.gpr .x7) s ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        if Spec.Gcm.tagLenOk tl ∧ T.take tl = bytesAt s.mem (s.gpr .x5) tl then (s₄.gpr .x0).setWidth 32 = 1
        else (s₄.gpr .x0).setWidth 32 = 0))
    (WP.ite _ ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s₄ hs₄ => ?_
    subst hs₄
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, sv₃, fun _ => ?_⟩
    rw [ite_eq_right (by simp [hok])]
    simp [gpr_write]
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := VG.Proof.AesGcm.AArch64.tagLenOk_le hok
    have x12₃ : s₃.gpr .x12 = s.gpr .x5 := by rw [r₃.others _ (by decide), x12₂]
    have x28₃ : s₃.gpr .x28 = BitVec.ofNat 64 tl := by rw [r₃.others _ (by decide), x28₂']
    refine WP.seq (WP.mono (tagIn_ok he₃.x19 x12₃ x28₃ hle (by rw [r₃.rd, r₃.wr, rd₂, wr₂]; exact tR)
      he₃.perm.w (dtw.sub_right (Region.sub_prefix (by decide))))
      fun s₄ ⟨in₄, f₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
    have he₄ : Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp s₄ := he₃.keep (fun r hr => og₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
    have hk₄ : Kept s₃.gpr s₄ := Kept.of_others (fun _ _ => rfl) og₄
    have F₄ : Frame [savedR (s.gpr .x7), ⟨s.gpr .x7, 16⟩] s.mem s₄.mem :=
      (fsv.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).trans
        (by rw [← m₃]; exact f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp,
          fun _ h => h⟩)
    obtain ⟨hc₄, hj₄, hH₄, hA₄⟩ := VG.Proof.AesGcm.AArch64.fin_inv L (VG.Proof.AesGcm.AArch64.tag16_inv L) F₄ hR (x := ghashInput a c)
    have x22₄ : s₄.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hk₄ .x22 (by decide), r₃.others _ (by decide), x22₂]
    have x26₄ : s₄.gpr .x26 = BitVec.ofNat 64 a.length := by
      rw [hk₄ .x26 (by decide), r₃.others _ (by decide), x26₂, h3]
    have x27₄ : s₄.gpr .x27 = BitVec.ofNat 64 c.length := by
      rw [hk₄ .x27 (by decide), r₃.others _ (by decide), x27₂, h4]
    refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finBody_ok L v (.inr rfl) (a := a) (c := c) (H := ctxH s.mem (s.gpr .x0)) he₄ hk₄
      x22₄ hR x26₄ x27₄ hc hH₄) fun s₅ ⟨he₅, hk₅, f₅, out₅⟩ => ?_)
    have x28₅ : s₅.gpr .x28 = BitVec.ofNat 64 tl := by rw [hk₅ .x28 (by decide), x28₃]
    refine WP.seq (WP.mono (cmpSeg_ok L he₅ hk₅ x28₅ hle) fun s₆ ⟨x10₆, he₆, _, _, f₆⟩ => ?_)
    refine WP.mono (verRet_ok
      (b := decide (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl))
      (by rw [x10₆]; by_cases hp : bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl =
            bytesAt s₅.mem (s.gpr .x7) tl <;> simp [hp]))
      fun s₇ ⟨x0₇, r₇⟩ =>
        ⟨he₆.of_regs r₇, by
          rw [r₇.mem]
          exact (((sv₃.frame f₄ (saved_tag16 L)).frame f₅ (VG.Proof.AesGcm.AArch64.saved_finFrame L (.inr rfl))).frame f₆ (saved_cmp L)),
          fun ha => ?_⟩
    have hT₅ : bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) 16 = T := by
      rw [out₅ (hA₄ ha), hc₄, hj₄, ← hT]
    have hW₅ : bytesAt s₅.mem (s.gpr .x7) tl = bytesAt s.mem (s.gpr .x5) tl := by
      have dW : ∀ r ∈ VG.Proof.AesGcm.AArch64.finFrame (s.gpr .x2) (s.gpr .x7) 112, (⟨s.gpr .x7, tl⟩ : Region).Disjoint r := by
        intro r hr
        refine Region.Disjoint.sub_left ?_ (Region.sub_prefix hle)
        have ww : ∀ e j, 16 ≤ e → e + j ≤ 2560 →
            (⟨s.gpr .x7, 16⟩ : Region).Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 e, j⟩ := fun e j h₁ h₂ => by
          simpa using L.w_w (a := 0) (n := 16) (d := e) (k := j) (.inl h₁) (by decide) h₂
        rcases List.mem_append.mp hr with hr | hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (L.sa.sub_left (Lay.stSub (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (L.sa.sub_left (Region.sub_prefix (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
      rw [bytesAt_frame f₅ dW (by omega), in₄, m₃]
      refine bytesAt_frame fsv (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact dtw.sub_right (Lay.wSub (by decide))
    have hb : (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl) ↔
        T.take tl = bytesAt s.mem (s.gpr .x5) tl := by
      rw [← bytesAt_take _ _ hle, hT₅, hW₅]
    by_cases hp : T.take tl = bytesAt s.mem (s.gpr .x5) tl
    · rw [ite_eq_left ⟨hok, hp⟩]
      have hb' := hb.mpr hp
      simp only [hb', decide_true, ite_true] at x0₇
      rw [x0₇]; rfl
    · rw [ite_eq_right (fun h => hp h.2)]
      have hb' : ¬ (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl) :=
        fun h => hp (hb.mp h)
      simp only [hb', decide_false, Bool.false_eq_true, ite_false] at x0₇
      rw [x0₇]; rfl
  refine WP.mono (exit_ok he₄.x19 he₄.sp (covers_left he₄.perm.w) sv₄) fun s' ⟨ga, _, hx0, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hx0]
  exact post₄ ha

theorem streamVerify_wp (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧ streamVerifyAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  let tl := (s.gpr .x6).toNat
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2).take tl = bytesAt s.mem (s.gpr .x5) tl then
        (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0)
    (VG.Proof.AesGcm.AArch64.ver_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (VG.Proof.AesGcm.AArch64.ver_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have ht : Spec.Gcm.fullTag ciph h iv a c =
      toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
        [ofBytes (lensBlock a.length c.length)] ^^^
        ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) := by
    rw [Proof.Gcm.fullTag_eq, hj]; rfl
  show if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h iv a c).take tl = _ then _ else _
  rw [ht]
  exact hout habs

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.FinCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish` and `_verify` are constant time

Untrusted: everything here is checked by Lean. The code around `finBody` by
the taint analysis (the tag length and the tags' addresses are public, and
`cmpSeg` compares without a branch); `finBody` by `finBody_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `finBody o`, run, from the state after the entry. -/
theorem finBody_env (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W) {o : Nat} (ho : o = 0 ∨ o = 112)
    {k : Reg → BitVec 64} {R A P : Nat} {τ : State} (he : Env Ctx St W SP τ) (hk : Kept k τ)
    (h22 : τ.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26 : τ.gpr .x26 = BitVec.ofNat 64 A) (h27 : τ.gpr .x27 = BitVec.ofNat 64 P) (hP : P < 2 ^ 64) :
    WP isa (finBody v.callees o) τ fun τ' => Env Ctx St W SP τ' ∧ Kept k τ' ∧
      Frame (VG.Proof.AesGcm.AArch64.finFrame St W o) τ.mem τ'.mem :=
  WP.mono (VG.Proof.AesGcm.AArch64.finBody_ok L v ho (a := Spec.Gcm.zeros A) (c := Spec.Gcm.zeros P)
    (H := blockAt τ.mem (Ctx + BitVec.ofNat 64 240)) he hk h22 hR
    (by rw [Proof.Gcm.length_zeros]; exact h26) (by rw [Proof.Gcm.length_zeros]; exact h27)
    (by rw [Proof.Gcm.length_zeros]; exact hP) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa streamFinishAArch64.pre streamFinishAArch64.pub (streamFinish v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, qsp⟩ := hq
  have p₁ : finPre σ₁ := h₁
  have p₂ : finPre σ₂ := h₂
  obtain ⟨L, perm₁, hR, -, -⟩ := VG.Proof.AesGcm.AArch64.lay_of_fin p₁
  obtain ⟨-, perm₂, -, -, -⟩ := VG.Proof.AesGcm.AArch64.lay_of_fin p₂
  rw [← q0, ← q2, ← q6] at perm₂
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := hR
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6] qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.finishEntry_ok rfl rfl rfl perm₁) (VG.Proof.AesGcm.AArch64.finishEntry_ok q0.symm q2.symm q6.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x22₁, x26₁, x27₁, x28₁, _, _, _⟩ ⟨e₂, k₂, x22₂, x26₂, x27₂, x28₂, _, _, _⟩ => ?_
  rw [← qsp] at e₂
  rw [← q1] at x22₂
  rw [← q3] at x26₂
  rw [← q4] at x27₂
  rw [← q5] at x28₂
  have a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine rel_seq (VG.Proof.AesGcm.AArch64.finBody_rel L v (.inl rfl) e₁ e₂ k₁ k₂ x22₁ x22₂ hRb a26₁ a26₂ a27₁ a27₂
      (σ₁.gpr .x3).isLt (σ₁.gpr .x4).isLt)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inl rfl) e₁ k₁ x22₁ hRb a26₁ a27₁ (σ₁.gpr .x4).isLt)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inl rfl) e₂ k₂ x22₂ hRb a26₂ a27₂ (σ₁.gpr .x4).isLt) fun τ₁' τ₂' f₁ f₂ => ?_
  have c28₁ : τ₁'.gpr .x28 = σ₁.gpr .x5 := (f₁.2.1 .x28 (by decide)).trans x28₁
  have c28₂ : τ₂'.gpr .x28 = σ₁.gpr .x5 := (f₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [f₁.1.sp, f₂.1.sp])
    (by agree_tac [f₁.1.x19, f₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa streamVerifyAArch64.pre streamVerifyAArch64.pub (streamVerify v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩ := hq
  have p₁ : verPre σ₁ := h₁
  have p₂ : verPre σ₂ := h₂
  obtain ⟨L, perm₁, hR, tR₁, dtw⟩ := VG.Proof.AesGcm.AArch64.lay_of_ver p₁
  obtain ⟨-, perm₂, -, tR₂, -⟩ := VG.Proof.AesGcm.AArch64.lay_of_ver p₂
  rw [← q0, ← q2, ← q7] at perm₂
  rw [← q5, ← q6] at tR₂
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := hR
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.verEntry_ok rfl rfl rfl perm₁) (VG.Proof.AesGcm.AArch64.verEntry_ok q0.symm q2.symm q7.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x22₁, x26₁, x27₁, x28₁, x12₁, _, rd₁, wr₁⟩
      ⟨e₂, k₂, x22₂, x26₂, x27₂, x28₂, x12₂, _, rd₂, wr₂⟩ => ?_
  rw [← qsp] at e₂
  rw [← q1] at x22₂
  rw [← q3] at x26₂
  rw [← q4] at x27₂
  rw [← q6] at x28₂
  rw [← q5] at x12₂
  rw [← rd₁, ← wr₁] at tR₁
  rw [← rd₂, ← wr₂] at tR₂
  have t28₁ : τ₁.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have t28₂ : τ₂.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl := (σ₁.gpr .x6).isLt
  refine rel_seq (rel_taint [.x28] (by rw [e₁.sp, e₂.sp]) (by agree_tac [t28₁, t28₂]) ⟨_, by taint_decide⟩)
    (tagLenOk_ok τ₁ t28₁ htl) (tagLenOk_ok τ₂ t28₂ htl) fun τ₁' τ₂' ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  have ge₁ := e₁.of_regs r₁
  have ge₂ := e₂.of_regs r₂
  have gk₁ := k₁.of_others r₁.others
  have gk₂ := k₂.of_others r₂.others
  -- The branch and its run.
  have ev : ∀ {τ : State}, τ.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      isa.eval (.zero .x .x9) τ =
        some (decide ((if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) = 0)) :=
    fun h => eval_zero h (by split <;> decide)
  have tIn : ∀ {τ' : State} (hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true),
      Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' → τ'.gpr .x12 = σ₁.gpr .x5 →
      τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa VG.Impl.AesGcm.AArch64.tagIn τ' fun τ'' => Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' ∧ Kept τ'.gpr τ'' :=
    fun hok he h12 h28 hr => WP.mono (tagIn_ok he.x19 h12 h28 (VG.Proof.AesGcm.AArch64.tagLenOk_le hok) hr he.perm.w
      (dtw.sub_right (Region.sub_prefix (by decide)))) fun _ ⟨_, _, og, sp, rd, wr⟩ =>
        ⟨he.keep (fun r hr => og r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, Kept.of_others (fun _ _ => rfl) og⟩
  have run : ∀ {τ' : State} {k : Reg → BitVec 64}, Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' →
      Kept k τ' → τ'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      τ'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat → τ'.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat →
      τ'.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat → τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      τ'.gpr .x12 = σ₁.gpr .x5 → Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa (.ite (.zero .x .x9) (.block [imm .x0 0])
        (.seq VG.Impl.AesGcm.AArch64.tagIn (.seq (finBody v.callees uO) (.seq cmpSeg (.block verRet))))) τ' fun τ'' =>
        Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' := by
    intro τ' k he hk h9 h22 h26 h27 h28 h12 hr
    refine WP.ite _ (ev h9) (fun _ => ?_) (fun hf => ?_)
    · exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'
        exact he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl
    · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true := by
        revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat <;> simp
      refine WP.seq (WP.mono (tIn hok he h12 h28 hr) fun τ₃ ⟨he₃, hk₃⟩ => ?_)
      refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finBody_env v L (.inr rfl) he₃ hk₃ (by rw [hk₃ .x22 (by decide), h22]) hRb
        (by rw [hk₃ .x26 (by decide), h26]) (by rw [hk₃ .x27 (by decide), h27]) (σ₁.gpr .x4).isLt)
        fun τ₄ ⟨he₄, hk₄, _⟩ => ?_)
      refine WP.seq (WP.mono (cmpSeg_ok L he₄ hk₄ (by rw [hk₄ .x28 (by decide), h28])
        (VG.Proof.AesGcm.AArch64.tagLenOk_le hok)) fun τ₅ ⟨x10₅, he₅, _, _, _⟩ => ?_)
      exact WP.mono (verRet_ok (b := decide (bytesAt τ₄.mem (σ₁.gpr .x7 + BitVec.ofNat 64 112)
        (σ₁.gpr .x6).toNat = bytesAt τ₄.mem (σ₁.gpr .x7) (σ₁.gpr .x6).toNat))
        (by rw [x10₅]; simp only [decide_eq_true_eq])) fun _ ⟨_, r⟩ => he₅.of_regs r
  have g9₁ : τ₁'.gpr .x9 = _ := x9₁
  have g9₂ : τ₂'.gpr .x9 = _ := x9₂
  have o22₁ : τ₁'.gpr .x22 = _ := (r₁.others .x22 (by decide)).trans x22₁
  have o22₂ : τ₂'.gpr .x22 = _ := (r₂.others .x22 (by decide)).trans x22₂
  have o26₁ : τ₁'.gpr .x26 = _ := (r₁.others .x26 (by decide)).trans a26₁
  have o26₂ : τ₂'.gpr .x26 = _ := (r₂.others .x26 (by decide)).trans a26₂
  have o27₁ : τ₁'.gpr .x27 = _ := (r₁.others .x27 (by decide)).trans a27₁
  have o27₂ : τ₂'.gpr .x27 = _ := (r₂.others .x27 (by decide)).trans a27₂
  have o28₁ : τ₁'.gpr .x28 = _ := (r₁.others .x28 (by decide)).trans t28₁
  have o28₂ : τ₂'.gpr .x28 = _ := (r₂.others .x28 (by decide)).trans t28₂
  have o12₁ : τ₁'.gpr .x12 = _ := (r₁.others .x12 (by decide)).trans x12₁
  have o12₂ : τ₂'.gpr .x12 = _ := (r₂.others .x12 (by decide)).trans x12₂
  have oR₁ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₁'.rd ++ τ₁'.wr) := by rw [r₁.rd, r₁.wr]; exact tR₁
  have oR₂ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₂'.rd ++ τ₂'.wr) := by rw [r₂.rd, r₂.wr]; exact tR₂
  refine rel_seq (rel_ite (ev g9₁) (ev g9₂) (fun _ => ?_) (fun hf => ?_))
    (run ge₁ gk₁ g9₁ o22₁ o26₁ o27₁ o28₁ o12₁ oR₁) (run ge₂ gk₂ g9₂ o22₂ o26₂ o27₂ o28₂ o12₂ oR₂)
    fun τ₁ τ₂ f₁ f₂ => ?_
  · exact rel_taint [] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true := by
      revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat <;> simp
    refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [ge₁.sp, ge₂.sp])
        (by agree_tac [ge₁.x19, ge₂.x19, o28₁, o28₂, o12₁, o12₂]) ⟨_, by taint_decide⟩)
      (tIn hok ge₁ o12₁ o28₁ oR₁) (tIn hok ge₂ o12₂ o28₂ oR₂) fun τ₃ τ₃' ⟨he₃, hk₃⟩ ⟨he₃', hk₃'⟩ => ?_
    refine rel_seq (VG.Proof.AesGcm.AArch64.finBody_rel L v (.inr rfl) he₃ he₃' hk₃ hk₃'
        (by rw [hk₃ .x22 (by decide), o22₁]) (by rw [hk₃' .x22 (by decide), o22₂]) hRb
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃' .x26 (by decide), o26₂])
        (by rw [hk₃ .x27 (by decide), o27₁]) (by rw [hk₃' .x27 (by decide), o27₂])
        (σ₁.gpr .x3).isLt (σ₁.gpr .x4).isLt)
      (VG.Proof.AesGcm.AArch64.finBody_env v L (.inr rfl) he₃ hk₃ (by rw [hk₃ .x22 (by decide), o22₁]) hRb
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃ .x27 (by decide), o27₁]) (σ₁.gpr .x4).isLt)
      (VG.Proof.AesGcm.AArch64.finBody_env v L (.inr rfl) he₃' hk₃' (by rw [hk₃' .x22 (by decide), o22₂]) hRb
        (by rw [hk₃' .x26 (by decide), o26₂]) (by rw [hk₃' .x27 (by decide), o27₂]) (σ₁.gpr .x4).isLt)
      fun τ₄ τ₄' ⟨he₄, hk₄, _⟩ ⟨he₄', hk₄', _⟩ => ?_
    have c28₁ : τ₄.gpr .x28 = _ := (hk₄ .x28 (by decide)).trans o28₁
    have c28₂ : τ₄'.gpr .x28 = _ := (hk₄' .x28 (by decide)).trans o28₂
    refine rel_seq (rel_taint [.x19, .x28] (by rw [he₄.sp, he₄'.sp])
        (by agree_tac [he₄.x19, he₄'.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩)
      (cmpSeg_ok L he₄ hk₄ c28₁ (VG.Proof.AesGcm.AArch64.tagLenOk_le hok)) (cmpSeg_ok L he₄' hk₄' c28₂ (VG.Proof.AesGcm.AArch64.tagLenOk_le hok))
      fun τ₅ τ₅' ⟨_, he₅, _, _, _⟩ ⟨_, he₅', _, _, _⟩ => ?_
    exact rel_taint [] (by rw [he₅.sp, he₅'.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact rel_taint [.x19] (by rw [f₁.sp, f₂.sp]) (by agree_tac [f₁.x19, f₂.x19]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry`. -/
section

/-!
# AES-GCM on AArch64: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. `work` comes from the stack
(`ldrSp_ok`); the entry saves our caller's registers there, keeps the arguments it needs
later at `W + 216` (`oneEntry_ok`, `OneE`), and puts the state at
`W + 16` (`oneLay`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x4)).writeW (W + BitVec.ofNat 64 224) (g .x5)).writeW
    (W + BitVec.ofNat 64 232) (g .x6)).writeW (W + BitVec.ofNat 64 240) (g .x7)

/-- What the entry keeps at `W + 128`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 128⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) :
    (VG.Proof.AesGcm.AArch64.entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [VG.Proof.AesGcm.AArch64.entryR W] m (VG.Proof.AesGcm.AArch64.entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) := VG.Proof.AesGcm.AArch64.entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (VG.Proof.AesGcm.AArch64.entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (VG.Proof.AesGcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x4 ∧
    (VG.Proof.AesGcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x5 ∧
    (VG.Proof.AesGcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x6 ∧
    (VG.Proof.AesGcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x7 := by
  simp only [VG.Proof.AesGcm.AArch64.entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- The load of a stack argument, at `sp + k`. -/
theorem ldrSp_ok {s : State} {t : Reg} {k : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = V)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.ldrSp t k] s = some s' ∧ s'.gpr t = V ∧ (∀ r, r ≠ t → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by arun [hsp, hk], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  rw [← hV]
  simp [gpr_write, Mem.readW]

/-- After the entry, with `work` at `sp + k`. -/
theorem oneEntry_ok {s : State} {Ctx W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) (hCtx : s.gpr .x0 = Ctx)
    (hperm : Perm Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block (oneEntry k)) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x22 = s.gpr .x1 ∧ s'.gpr .x23 = s.gpr .x2 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = 0 ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x6 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x7 ∧
      Frame [VG.Proof.AesGcm.AArch64.entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x9₀, g₀, sp₀, m₀, rd₀, wr₀⟩ := VG.Proof.AesGcm.AArch64.ldrSp_ok (t := .x9) hk hW hsp
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := hperm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 2560) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x23₂, x24₂, x26₂, x27₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x6 .x19 dataO, .str .x .x7 .x19 lenO, mov .x23 .x2,
        mov .x24 .x3, mov .x26 .x3, imm .x27 0] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = s.gpr .x1 ∧
      s₂.gpr .x23 = s.gpr .x2 ∧ s₂.gpr .x24 = s.gpr .x3 ∧ s₂.gpr .x26 = s.gpr .x3 ∧ s₂.gpr .x27 = 0 ∧
      s₂.sp = s₁.sp ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 216) (s.gpr .x4)).writeW (W + BitVec.ofNat 64 224)
        (s.gpr .x5)).writeW (W + BitVec.ofNat 64 232) (s.gpr .x6)).writeW (W + BitVec.ofNat 64 240) (s.gpr .x7) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, g₀ r hr]
    have x9₁ : s₁.gpr .x9 = W := by rw [g₁, x9₀]
    have w₁ := w 216 (by decide)
    have w₂ := w 224 (by decide)
    have w₃ := w 232 (by decide)
    have w₄ := w 240 (by decide)
    refine ⟨_, by arun [x9₁, BitVec.add_zero, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
    · simp [gpr_write, x9₁]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), hCtx]
    · simp [gpr_write, gx .x1 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write, gx .x3 (by decide)]
    · simp [gpr_write, gx .x3 (by decide)]
    · simp [gpr_write]
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, gpr_write, ite_true, ite_false, reduceCtorEq,
        gx .x4 (by decide), gx .x5 (by decide), gx .x6 (by decide), gx .x7 (by decide), x9₁]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hm : s₂.mem = VG.Proof.AesGcm.AArch64.entryMem s.mem W s₀.gpr := by
    rw [m₂, m₁, m₀, VG.Proof.AesGcm.AArch64.entryMem, g₀ .x4 (by decide), g₀ .x5 (by decide), g₀ .x6 (by decide), g₀ .x7 (by decide)]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := VG.Proof.AesGcm.AArch64.entryMem_slot s.mem W s₀.gpr
  rw [g₀ .x4 (by decide)] at e₁
  rw [g₀ .x5 (by decide)] at e₂
  rw [g₀ .x6 (by decide)] at e₃
  rw [g₀ .x7 (by decide)] at e₄
  refine ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁, sp₀], hperm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])⟩,
    x22₂, x23₂, x24₂, x26₂, x27₂, by rw [hm]; exact e₁, by rw [hm]; exact e₂, by rw [hm]; exact e₃,
    by rw [hm]; exact e₄, by rw [hm]; exact VG.Proof.AesGcm.AArch64.entryMem_frame _ _ _,
    by rw [hm]; exact VG.Proof.AesGcm.AArch64.entryMem_saved _ _ fun p hp => g₀ p.1 (by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [rd₂, rd₁, rd₀], by rw [wr₂, wr₁, wr₀]⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Front`. -/
section

/-!
# AES-GCM on AArch64: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. After the entry, `j0` starts
the state at `W + 16` for the nonce, `oneAad` absorbs the additional data and
`encPrep` sets up the text's arguments from the slots the entry wrote
(`front_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Proof.Gcm (Absorbed)

/-- The regions `j0` and `oneAad` write. -/
abbrev frontFrame (St W : Addr) : List Region := j0Frame St W ++ absFrame St W 16

/-- The slots stay where they are, outside a frame apart from them. -/
theorem slot_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : Addr}
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r) {d : Nat} (h₁ : 216 ≤ d)
    (h₂ : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub _ h₁ (by omega))) (by decide)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem slots_j0Frame : ∀ r ∈ j0Frame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (d := 216) (k := 40) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_absFrame : ∀ r ∈ absFrame St W 16, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_frontFrame : ∀ r ∈ VG.Proof.AesGcm.AArch64.frontFrame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact VG.Proof.AesGcm.AArch64.slots_j0Frame L r hr
  · exact VG.Proof.AesGcm.AArch64.slots_absFrame L r hr

theorem saved_frontFrame : ∀ r ∈ VG.Proof.AesGcm.AArch64.frontFrame St W, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_j0Frame L r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- After `encPrep`, from `s₀`. -/
structure Front (Ctx St W SP : Addr) (H : Block) (iv a : List Byte) (D : Addr) (n : Nat) (s₀ : State)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = s₀.gpr .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  abs : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H a
  frame : Frame (VG.Proof.AesGcm.AArch64.frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `j0`, `oneAad` and `encPrep`. -/
theorem front_ok (v : GcmImpl) {s₀ : State} {k : Reg → BitVec 64} {H : Block} {Np A D : Addr} {nl al n : Nat}
    (he : Env Ctx St W SP s₀) (hk : Kept k s₀) (h23 : s₀.gpr .x23 = Np) (h24 : s₀.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s₀.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s₀.gpr .x27 = 0)
    (hnon : DataOk St W s₀ Np nl) (haad : DataOk St W s₀ A al)
    (hH : blockAt s₀.mem (Ctx + BitVec.ofNat 64 240) = H)
    (sA : s₀.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s₀.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s₀.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s₀.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', VG.Proof.AesGcm.AArch64.Front Ctx St W SP H (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) D n s₀ s' → WP isa rest s' Q) :
    WP isa (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) s₀ Q := by
  have hlt := haad.lt
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L v ⟨he, hk, h23, h24, h26, h27, hnon, hH⟩))
    fun s₁ ⟨h₁, rd₁, wr₁⟩ => ?_)
  have r₁ (d : Nat) (h : d + 8 ≤ 2560) := h₁.env.perm.wR h
  obtain ⟨s₂, run₂, x23₂, x24₂, x25₂, r₂⟩ : ∃ s₂, runBlock isa [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO,
      imm .x25 0] s₁ = some s₂ ∧ s₂.gpr .x23 = A ∧ s₂.gpr .x24 = BitVec.ofNat 64 al ∧
      s₂.gpr .x25 = BitVec.ofNat 64 0 ∧ Regs [.x23, .x24, .x25] s₁ s₂ := by
    have e₁ := VG.Proof.AesGcm.AArch64.slot_kept h₁.frame (VG.Proof.AesGcm.AArch64.slots_j0Frame L) (d := 216) (by decide) (by decide)
    have e₂ := VG.Proof.AesGcm.AArch64.slot_kept h₁.frame (VG.Proof.AesGcm.AArch64.slots_j0Frame L) (d := 224) (by decide) (by decide)
    rw [sA] at e₁
    rw [sL] at e₂
    have q₁ := r₁ 216 (by decide)
    have q₂ := r₁ 224 (by decide)
    refine ⟨_, by arun [h₁.env.x19, q₁, q₂], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₁]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₂]; rfl
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩))
  have he₂ := h₁.env.of_regs r₂
  have hk₂ := h₁.kept.of_others r₂.others
  have hd₂ : DataOk St W s₂ A al := haad.of_eq (by rw [r₂.rd, rd₁]) (by rw [r₂.wr, wr₁])
  have hIn : AbsIn Ctx St W SP k H [] A al 0 s₂ :=
    ⟨he₂, hk₂, x23₂, x24₂, x25₂, rfl, hd₂, by rw [r₂.mem]; exact h₁.hH⟩
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hIn)) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_
  have f₃ : Frame (VG.Proof.AesGcm.AArch64.frontFrame St W) s₀.mem s₃.mem :=
    (h₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have q (d : Nat) (h : d + 8 ≤ 2560) := h₃.env.perm.wR h
  obtain ⟨s₄, run₄, x25₄, x26₄, x27₄, x28₄, r₄⟩ : ∃ s₄, runBlock isa encPrep s₃ = some s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s₄.gpr .x26 = BitVec.ofNat 64 n ∧ s₄.gpr .x27 = 0 ∧
      s₄.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s₃ s₄ := by
    have e₂ := VG.Proof.AesGcm.AArch64.slot_kept f₃ (VG.Proof.AesGcm.AArch64.slots_frontFrame L) (d := 224) (by decide) (by decide)
    have e₃ := VG.Proof.AesGcm.AArch64.slot_kept f₃ (VG.Proof.AesGcm.AArch64.slots_frontFrame L) (d := 232) (by decide) (by decide)
    have e₄ := VG.Proof.AesGcm.AArch64.slot_kept f₃ (VG.Proof.AesGcm.AArch64.slots_frontFrame L) (d := 240) (by decide) (by decide)
    rw [sL] at e₂
    rw [sD] at e₃
    rw [sN] at e₄
    have q₂ := q 224 (by decide)
    have q₃ := q 232 (by decide)
    have q₄ := q 240 (by decide)
    refine ⟨_, by simp only [encPrep]; arun [h₃.env.x19, q₂, q₃, q₄], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 224#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, e₂,
        show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 240#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, e₄]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 232#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, e₃]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, hr s₄ ⟨h₃.env.of_regs r₄, ?_, ?_, x26₄, x27₄, x28₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
  · rw [r₄.others _ (by decide), h₃.kept .x22 (by decide), ← hk .x22 (by decide)]
  · rw [x25₄, length_bytesAt]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩), r₂.mem, h₁.j0]
  · rw [r₄.mem, blockAt_frame h₃.frame (ctx_absFrame L (.inr rfl)), r₂.mem, h₁.hH]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => (ctr_absFrame L r hr).sub_left
      (Region.sub_prefix (by decide))), r₂.mem, h₁.cb]
  · rw [r₄.mem]
    have := h₃.abs (Proof.Gcm.absorbed_nil H (by rw [r₂.mem]; exact h₁.y))
    rw [List.nil_append, r₂.mem, bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact haad.st
      · exact haad.w.sub_right (Lay.wSub (by decide))
      · exact haad.w.sub_right (Lay.wSub (by decide))) (by omega)] at this
    exact this
  · rw [r₄.mem]; exact f₃
  · rw [r₄.rd, rd₃, r₂.rd, rd₁]
  · rw [r₄.wr, wr₃, r₂.wr, wr₁]

end

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.InitCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls by
the taint analysis, from the public arguments and the registers the
correctness proof pins (`init1_ok`, `init2_ok`); the calls by their callees'
proofs, with the arguments those proofs give.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The block before the call of `vg_aes_expand_key_scratch`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} {L : Nat} (hK : s.gpr .x0 = K) (hLn : (s.gpr .x1).toNat = L)
    (hCtx : s.gpr .x2 = Ctx) (hW : s.gpr .x3 = W) (hrd : s.rd = [⟨K, L⟩])
    (hwr : s.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩]) (d_kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩)
    (d_ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩) (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    WP isa (.block initSeg1) s fun s₂ => KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.gpr .x19 = W ∧
      s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧ s₂.sp = s.sp ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x3 hW pW
  have hsi : s.gpr .x1 = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x21₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x3, mov .x21 .x2, .lsr .x .x22 .x1 2, .addImm .x .x22 .x22 6, ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, hsi, BitVec.setWidth_eq]
      exact rounds_of_len hL
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hsi]
    · simp [gpr_write, g₁, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  refine ⟨⟨x0₂, x1₂, x2₂, x3₂, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩, x19₂, x21₂, x22₂, by rw [sp₂, sp₁], rd₂', wr₂'⟩
  · rw [rd₂', wr₂', hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
  · rw [wr₂']; exact covers_cons (covers_prefix pC (by decide)) pS

/-- The block before the call of `vg_aes_ctr32`. -/
theorem init2_ok {s : State} {Ctx W : Addr} {R : Nat} (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = Ctx)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR' : R = 10 ∨ R = 12 ∨ R = 14)
    (pC : Covers [⟨Ctx, 256⟩] s.wr) (pW : Covers [⟨W, 2560⟩] s.wr) (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (wc : Ctx.toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block initSeg2) s fun s₄ =>
      CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      s₄.gpr .x19 = W ∧ s₄.sp = s.sp := by
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s₄, run₄, x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s = some s₄ ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .x3 = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s s₄ ∧
      s₄.sp = s.sp ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [h19, h21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, h21]
    · simp [gpr_write, h22]
    · simp [gpr_write, h19]
    · simp [gpr_write, h21]
    · simp [gpr_write]
    · simp [gpr_write, h19]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [og₄ _ (by decide), h19], sp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, hR', ?_, by decide, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
  · simpa using dCW 0 240 (by decide) 96 16 (by decide)
  · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact dCW 240 16 (by decide) 512 2048 (by decide)
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide))) (covers_cons
      (covers_left (covers_off pC' (by decide) (by decide))) (covers_left (covers_off pW' (by decide) (by decide)))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_cons (covers_off pC' (by decide) (by decide))
      (covers_off pW' (by decide) (by decide)))

theorem init_ct (v : GcmImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  simp only [initAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q3] at h₂
  obtain ⟨hrd₁, hwr₁, d_kc, d_ks, d_cs, wc, ws, hL⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hK : σ₁.gpr .x0 = K at *
  generalize hLn : (σ₁.gpr .x1).toNat = L at *
  generalize hCtx : σ₁.gpr .x2 = Ctx at *
  generalize hW : σ₁.gpr .x3 = W at *
  have hR' : Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
    rcases hL with rfl | rfl | rfl <;> decide
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [hK, hCtx, hW, ← q0, q1, ← q2, ← q3])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.init1_ok hK hLn hCtx hW hrd₁ hwr₁ d_kc d_ks d_cs hL)
    (VG.Proof.AesGcm.AArch64.init1_ok q0.symm (by rw [← q1, hLn]) q2.symm q3.symm hrd₂ hwr₂ d_kc d_ks d_cs hL)
    fun τ₁ τ₂ ⟨k₁, x19₁, x21₁, x22₁, sp₁, rd₁, wr₁⟩ ⟨k₂, x19₂, x21₂, x22₂, sp₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_key v.key k₁ k₂ (by rw [sp₁, sp₂, qsp])) (key_call v.key k₁) (key_call v.key k₂)
    fun τ₁' τ₂' g₁ g₂ => ?_
  have pv : ∀ {σ τ τ' : State}, σ.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩] → τ.wr = σ.wr →
      KeyPost τ K Ctx (W + BitVec.ofNat 64 512) L τ' → τ.gpr .x19 = W → τ.gpr .x21 = Ctx →
      τ.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) →
      WP isa (.block initSeg2) τ' fun s₄ => CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240)
        (W + BitVec.ofNat 64 512) (Spec.Aes.rounds (L / 4)) 1 ∧ s₄.gpr .x19 = W ∧ s₄.sp = τ'.sp :=
    fun hwr wr g h19 h21 h22 => VG.Proof.AesGcm.AArch64.init2_ok (by rw [g.saved .x19 (by decide) (by decide), h19])
      (by rw [g.saved .x21 (by decide) (by decide), h21]) (by rw [g.saved .x22 (by decide) (by decide), h22]) hR'
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp)) (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp))
      d_cs wc
  refine rel_seq (rel_taint [.x19, .x21, .x22] (by rw [g₁.sp, g₂.sp, sp₁, sp₂, qsp])
      (by agree_tac [g₁.saved .x19 (by decide) (by decide), g₂.saved .x19 (by decide) (by decide),
        g₁.saved .x21 (by decide) (by decide), g₂.saved .x21 (by decide) (by decide),
        g₁.saved .x22 (by decide) (by decide), g₂.saved .x22 (by decide) (by decide), x19₁, x19₂, x21₁, x21₂,
        x22₁, x22₂]) ⟨_, by taint_decide⟩)
    (pv hwr₁ wr₁ g₁ x19₁ x21₁ x22₁) (pv hwr₂ wr₂ g₂ x19₂ x21₂ x22₂) fun τ₁ τ₂ ⟨c₁, y₁, s₁'⟩ ⟨c₂, y₂, s₂'⟩ => ?_
  refine rel_seq (rel_ctr v.ctr c₁ c₂ (by rw [s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp]))
    (ctr_call v.ctr c₁) (ctr_call v.ctr c₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19] (by rw [e₁.sp, e₂.sp, s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp])
    (by agree_tac [e₁.saved .x19 (by decide) (by decide), e₂.saved .x19 (by decide) (by decide), y₁, y₂])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.OneShot`. -/
section

/-!
# AES-GCM on AArch64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. The layout of a one-shot call
(`oneLay`): the state at `W + 16`, inside `work`; everything the pieces
write is inside `work`, but for the data (`*_work`) and the tag.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `work`. -/
abbrev workR (W : Addr) : Region := ⟨W, 2560⟩

theorem stW {W : Addr} {d k : Nat} (h : d + k ≤ 80) :
    Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ (VG.Proof.AesGcm.AArch64.workR W) := by
  rw [add_ofNat_assoc]; exact Lay.wSub (by omega)

theorem keep_of_sub {rs : List Region} {W : Addr} (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.AesGcm.AArch64.workR W)) {X : Region}
    (hX : X.Disjoint (VG.Proof.AesGcm.AArch64.workR W)) : ∀ r ∈ rs, X.Disjoint r := fun r hr => hX.sub_right (hs r hr)

theorem entryR_work (W : Addr) : ∀ r ∈ [VG.Proof.AesGcm.AArch64.entryR W], Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem frontFrame_work (W : Addr) : ∀ r ∈ VG.Proof.AesGcm.AArch64.frontFrame (W + BitVec.ofNat 64 16) W, Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) := by
  intro r hr
  simp only [VG.Proof.AesGcm.AArch64.frontFrame, j0Frame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact VG.Proof.AesGcm.AArch64.stW (by decide)
  · exact VG.Proof.AesGcm.AArch64.stW (by decide)
  · exact Lay.wSub (by decide)

theorem finFrame_work (W : Addr) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.finFrame (W + BitVec.ofNat 64 16) W o, Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) := by
  intro r hr
  simp only [VG.Proof.AesGcm.AArch64.finFrame, tFrame, tagFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.AArch64.stW (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by omega)
  · exact Lay.wSub (by decide)

/-- The regions a body writes: in `work`, or the data. -/
theorem bodyFrame_work (W D : Addr) (n : Nat) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) ∨ r = ⟨D, n⟩ := by
  intro r hr
  simp only [bodyFrame, tFrame, crFrame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (VG.Proof.AesGcm.AArch64.stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr rfl
  · exact .inl (VG.Proof.AesGcm.AArch64.stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (VG.Proof.AesGcm.AArch64.stW (by decide))
  · exact .inl (VG.Proof.AesGcm.AArch64.stW (by decide))
  · exact .inl (Lay.wSub (by decide))

theorem keep_body {W D : Addr} {n : Nat} {X : Region} (hX : X.Disjoint (VG.Proof.AesGcm.AArch64.workR W)) (hD : X.Disjoint ⟨D, n⟩) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, X.Disjoint r := fun r hr => by
  rcases VG.Proof.AesGcm.AArch64.bodyFrame_work W D n r hr with h | rfl
  · exact hX.sub_right h
  · exact hD

/-- What `oneCore` gives, with `work` the `w`-th of the `n` arguments on the stack. -/
structure OneLay (s : State) (n w : Nat) : Prop where
  lay : Lay (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w)
  perm : Perm (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < n, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  nonce : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s w))
  aad : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s w))
  data : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s w))
  ctx : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s w))
  args : (args s n).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s w))
  nd : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  ad : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  cd : (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  nw : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  aw : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  dw : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  rounds : rounds (s.gpr .x1)
  nonceR : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr)
  aadR : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr)
  dataW : Covers [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.wr

theorem oneLay {s : State} {n w : Nat} (hs : oneCore n w s) : VG.Proof.AesGcm.AArch64.OneLay s n w := by
  simp only [oneCore] at hs
  obtain ⟨mc, mn, ma, mg, md, mw, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (VG.Proof.AesGcm.AArch64.workR (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_⟩, ⟨VG.Proof.AesGcm.AArch64.covers_mem (List.mem_append_left _ mc),
    covers_off (k := 2560) (covers_of_mem mw) (show 16 + 80 ≤ 2560 by decide) (by decide),
    covers_of_mem mw⟩,
    fun i hi => ?_, dnw, daw, ddw, dcw, dwa.symm, dnd, dad, dcd, wn, wa, wd, hR,
    VG.Proof.AesGcm.AArch64.covers_mem (List.mem_append_left _ mn), VG.Proof.AesGcm.AArch64.covers_mem (List.mem_append_left _ ma), covers_of_mem md⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · have := Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
      (by decide) (by decide)
    exact this
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Seal`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry and `front_ok`
start the state at `W + 16` and absorb the additional data, and keep `tag`
at `W + 248` (`entryStash_ok`); `encBody` encrypts the data and absorbs the
ciphertext, `finBody 0` writes the tag to `W`, and `tagOut` copies it to `tag`
(`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem slots_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact VG.Proof.AesGcm.AArch64.slots_absFrame L r hr

theorem saved_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tFrame L (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact saved_absFrame L (.inr rfl) r hr

theorem st0_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `finPrep`: the lengths from their slots. -/
theorem finPrep_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr))
    {al n : Nat} (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block finPrep) s fun s' => s'.gpr .x26 = BitVec.ofNat 64 al ∧ s'.gpr .x27 = BitVec.ofNat 64 n ∧
      Regs [.x26, .x27] s s' := by
  have q₁ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  have q₂ := in_off hr (show 240 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by simp only [finPrep]; arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl

/-- The load of the slot at `W + 248` into `x28`. -/
theorem ldr28_ok {Ctx W SP : Addr} {V : BitVec 64} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = V) :
    WP isa (.block [.ldr .x .x28 .x19 tlO]) s fun s' => s'.gpr .x28 = V ∧ Regs [.x28] s s' := by
  have q := he.perm.wR (show 248 + 8 ≤ 2560 by decide)
  refine WP.run ⟨_, by arun [he.x19, q], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
  rw [show s.mem.read (W + 248#64) 8 = s.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, sT]; rfl

/-- `stashArg k`: the stack argument at `sp + k` kept at `W + 248` and in `x28`. -/
theorem stashArg_ok {s : State} {W : Addr} {k : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = V) :
    WP isa (.block (stashArg k)) s fun s' =>
      s'.gpr .x28 = V ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 248) V ∧
      Others [.x10, .x28] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w := in_off hw (show 248 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by simp only [stashArg]; arun [h19, hsp, w, hk], rfl⟩ fun s' hs' => ?_
  subst hs'
  have e : s.mem.read (s.sp + BitVec.ofNat 64 k) 8 = V := by rw [← hV]; rfl
  refine ⟨by simp [gpr_write, e], ?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, e]

/-- The entry of `seal` and `open`, with `work` at `sp + k`, and the stack argument at `sp + j`
kept at `W + 248` and in `x28`. -/
theorem entryStash_ok {s : State} {Ctx W : Addr} {k j : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (hj : j % 8 = 0 ∧ j < 32768) (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hspk : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (hspj : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 j) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 j) 64 = V)
    (hdj : (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (hCtx : s.gpr .x0 = Ctx) (hperm : Perm Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block (oneEntry k ++ stashArg j)) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x22 = s.gpr .x1 ∧ s'.gpr .x23 = s.gpr .x2 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = 0 ∧ s'.gpr .x28 = V ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x6 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x7 ∧
      s'.mem.readW (W + BitVec.ofNat 64 248) 64 = V ∧
      Frame [VG.Proof.AesGcm.AArch64.entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.AArch64.oneEntry_ok hk hW hspk hCtx hperm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ =>
      WP.mono (VG.Proof.AesGcm.AArch64.stashArg_ok (V := V) hj he₁.x19 he₁.perm.w (by rw [rd₁, wr₁, he₁.sp]; exact hspj)
        (by rw [he₁.sp, f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 j, 8⟩) (Region.contains_self _ _)
          (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) hdj) (by decide), hV]))
      fun s₂ ⟨x28₂, m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_)
  have so (d : Nat) (hd : d + 8 ≤ 248) : s₂.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [m₂, readW_writeW_other _ _ _ (.inl hd) (by omega) (by decide)]
  have g₂ : ∀ r ∈ [Reg.x22, .x23, .x24, .x26, .x27], s₂.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨he₁.keep (fun r hr => og₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
    by rw [g₂ .x22 (by simp), x22₁], by rw [g₂ .x23 (by simp), x23₁], by rw [g₂ .x24 (by simp), x24₁],
    by rw [g₂ .x26 (by simp), x26₁], by rw [g₂ .x27 (by simp), x27₁], x28₂,
    by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂], by rw [so 232 (by decide), sl₃],
    by rw [so 240 (by decide), sl₄], by rw [m₂, Mem.readW_writeW_self64], ?_, ?_, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (VG.Proof.AesGcm.AArch64.entry_contains W (by decide) (by decide))
  · rw [m₂]
    exact sv₁.frame (rs := [⟨W + BitVec.ofNat 64 248, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))

/-- `sealPre`'s common arguments. -/
theorem sealCore {s : State} (hs : sealPre s) : oneCore 2 1 s := by
  simp only [sealPre] at hs
  obtain ⟨hrd, hwr, dcd, dcw, dnd, dnw, dad, daw, -, ddw, dda, -, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩

/-- What `sealPre` gives. -/
theorem sealLay {s : State} (hs : sealPre s) :
    VG.Proof.AesGcm.AArch64.OneLay s 2 1 ∧ Covers [⟨stackArg s 0, 16⟩] s.wr ∧
      (⟨stackArg s 0, 16⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s 1)) ∧
      (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, 16⟩ := by
  have hs' := hs
  simp only [sealPre] at hs'
  obtain ⟨-, hwr, -, -, -, -, -, -, ddt, -, -, dtw, -⟩ := hs'
  exact ⟨VG.Proof.AesGcm.AArch64.oneLay (VG.Proof.AesGcm.AArch64.sealCore hs), covers_of_mem (by rw [hwr]; simp), dtw, ddt⟩

theorem seal_wp (v : GcmImpl) {s : State} (hs : sealAArch64.pre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨ol, tW, dtw, ddt⟩ := VG.Proof.AesGcm.AArch64.sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have h3 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x3)
  have h5 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x5)
  have h7 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x7)
  have hW8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  have hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := hsp 1 (by decide)
  have hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by decide)
  have darg : (⟨s.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s 1)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 0, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * 2⟩
    exact Region.sub_prefix (by decide)
  generalize hW : stackArg s 1 = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  have hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.entryStash_ok (k := 8) (j := 0) (V := Tg) (by decide) (by decide) hW8 hsp8 hsp0 hT0 darg
      hCtx perm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, _, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ => ?_)
  rw [hA] at sl₁
  rw [← h5] at sl₂
  rw [hD] at sl₃
  rw [← h7] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (VG.Proof.AesGcm.AArch64.workR W) := Lay.wSub (by decide)
  have kc := VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  have hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np nl :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  have haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩
  have iv₁ : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame f₁ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) dnW) (by omega)
  have a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) daW) (by omega)
  refine VG.Proof.AesGcm.AArch64.front_ok L v he₁ (fun _ _ => rfl : Kept s₁.gpr s₁) (x23₁.trans hNp) (by rw [x24₁, ← h3])
    (by rw [x26₁, ← h3]) x27₁ hnon haad hH₁ sl₁ sl₂ sl₃ sl₄ fun s₂ h₂ => ?_
  rw [iv₁, a₁] at h₂
  have x22₂ : s₂.gpr .x22 = BitVec.ofNat 64 R := by rw [h₂.x22, x22₁, ← hRR, VG.Proof.AesGcm.AArch64.ofNat_toNat']
  have hdat₂ : DataW Ctx (W + BitVec.ofNat 64 16) W s₂ D n :=
    ⟨⟨covers_left (by rw [h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [h₂.wr, wr₁]; exact dW, dcd⟩
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W s.sp s₂.gpr R n 0 D (bytesAt s.mem A al) [] (ctxH s.mem Ctx) s₂ :=
    ⟨h₂.env, fun _ _ => rfl, x22₂, hRb, h₂.x25, h₂.x26, h₂.x27, h₂.x28, rfl, by decide, hdat₂, h₂.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (encBody_ok L v hB (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx)
    (bytesAt s.mem Np nl))))) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨o₁, o₂, o₃⟩ := h₃.post h₂.abs (Proof.Gcm.ctr_zero _ _ _ _ h₂.cb)
  have slot₃ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [VG.Proof.AesGcm.AArch64.slot_kept h₃.frame (VG.Proof.AesGcm.AArch64.slots_bodyFrame L ddW) h₁ h₂', VG.Proof.AesGcm.AArch64.slot_kept h₂.frame (VG.Proof.AesGcm.AArch64.slots_frontFrame L) h₁ h₂']
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finPrep_ok (al := al) (n := n) h₃.env.x19 (covers_left h₃.env.perm.w)
    (by rw [slot₃ 224 (by decide) (by decide), sl₂]) (by rw [slot₃ 240 (by decide) (by decide), sl₄]))
    fun s₄ ⟨x26₄, x27₄, r₄⟩ => ?_)
  have he₄ := h₃.env.of_regs r₄
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.ldr28_ok (V := Tg) he₄ (by rw [r₄.mem, slot₃ 248 (by decide) (by decide), sl₅]))
    fun s₄' ⟨x28₄', r₄'⟩ => ?_)
  have he₄' := he₄.of_regs r₄'
  have x22₄ : s₄'.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₄'.others _ (by decide), r₄.others _ (by decide), h₃.kept .x22 (by decide), x22₂]
  have x26₄' : s₄'.gpr .x26 = BitVec.ofNat 64 al := by rw [r₄'.others _ (by decide), x26₄]
  have x27₄' : s₄'.gpr .x27 = BitVec.ofNat 64 n := by rw [r₄'.others _ (by decide), x27₄]
  have m₄ : s₄'.mem = s₃.mem := by rw [r₄'.mem, r₄.mem]
  have kcd : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    VG.Proof.AesGcm.AArch64.keep_body dcW dcd
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₃.frame kcd hRb, ciph_frame h₂.frame (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) dcW) hRb]
  have hD₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [bytesAt_frame h₂.frame (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.frontFrame_work W) ddW) (by omega),
      bytesAt_frame f₁ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) ddW) (by omega)]
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₂.frame (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) dcW) hRb]
  have hH₄ : blockAt s₄'.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [m₄, blockAt_frame h₃.frame fun r hr => (kcd r hr).sub_left (Lay.ctxSub (by decide)), h₂.hH]
  have hlen : ([] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n)).length = n := by
    rw [List.nil_append, Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.finBody_ok L v (.inl rfl) (a := bytesAt s.mem A al) (H := ctxH s.mem Ctx)
    (c := [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n))
    he₄' (fun _ _ => rfl) x22₄ hRb (by rw [x26₄', length_bytesAt]) (by rw [x27₄', hlen]) (by rw [hlen]; exact hnlt)
    hH₄)) fun s₅ ⟨⟨he₅, hk₅, f₅, out₅⟩, _, wr₅⟩ => ?_)
  have sv₅ : SavedAt s₅.mem W s := by
    have := (sv₁.frame h₂.frame (VG.Proof.AesGcm.AArch64.saved_frontFrame L)).frame h₃.frame (VG.Proof.AesGcm.AArch64.saved_bodyFrame L ddW)
    rw [← m₄] at this
    exact this.frame f₅ (VG.Proof.AesGcm.AArch64.saved_finFrame L (.inl rfl))
  have x28₅ : s₅.gpr .x28 = Tg := by rw [hk₅ .x28 (by decide), x28₄']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, r₄'.wr, r₄.wr, wr₃, h₂.wr, wr₁]
  refine WP.seq (WP.mono (tagOut_ok he₅.x19 x28₅ (covers_left he₅.perm.w) (by rw [wr₅']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₆ ⟨out₆, f₆, og₆, sp₆, rd₆, wr₆⟩ => ?_)
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₆ := he₅.keep (fun r hr => og₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem W s := sv₅.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₆.x19 he₆.sp (covers_left he₆.perm.w) sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  have hdata : bytesAt s₆.mem D n = gctr (ctxCiph s.mem Ctx R)
      (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₆ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ddt) (by omega),
      bytesAt_frame f₅ (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.finFrame_work W (.inl rfl)) ddW) (by omega), m₄, o₃, hc₂, hD₂,
      Proof.Gcm.gctr_eq]
    rfl
  have hj₄ : blockAt s₄'.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl) := by
    rw [m₄, blockAt_frame h₃.frame (VG.Proof.AesGcm.AArch64.st0_bodyFrame L ddW), h₂.j0]
  have htag := out₅ (by rw [m₄]; exact o₁)
  rw [add_ofNat_zero, m₄, hc₃, ← m₄, hj₄] at htag
  have he : [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n) = gctr (ctxCiph s.mem Ctx R)
        (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [List.nil_append, hc₂, hD₂, Proof.Gcm.gctr_eq]; rfl
  rw [he] at htag
  rw [hdata, out₆, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Open`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The entry also keeps
`tag_len` at `W + 248`; if §5.2.1.2 does not allow it, `open` returns 0.
Otherwise `tagIn` copies the received tag to `W`, `front_ok` starts the
state and absorbs the additional data,
`decAbs` absorbs the ciphertext, `finBody 112` writes the tag at `W + 112`,
`cmpSeg` compares it with the received one without a branch, and the data is
decrypted only if they are equal (`open_wp`), which is the one secret the
code branches on, as the contract allows.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `decAbs`: the additional data padded if this is the first text, and the
text absorbed. -/
theorem decAbs_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k R n P D a c H s) :
    WP isa (decAbs v.callees) s fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega)
  have hd₃ : DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have F₃ : Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₃.mem := by
    rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  refine WP.ite (decide (n = 0)) (eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
    have := abs₂ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₃ :=
      ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
    refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
      ⟨h₄.env, h₄.kept, h₄.x25,
        F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
        by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, ← hD₃]
    exact h₄.abs (by rw [m₃]; exact abs₂ ha)

end

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- The regions `openMain` writes, but the data. -/
abbrev omFrame (W : Addr) : List Region :=
  VG.Proof.AesGcm.AArch64.frontFrame (W + BitVec.ofNat 64 16) W ++ (tFrame (W + BitVec.ofNat 64 16) W 16 ++
    absFrame (W + BitVec.ofNat 64 16) W 16) ++ VG.Proof.AesGcm.AArch64.finFrame (W + BitVec.ofNat 64 16) W 112 ++
    [⟨W + BitVec.ofNat 64 256, 32⟩]

theorem omFrame_work (W : Addr) : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact VG.Proof.AesGcm.AArch64.finFrame_work W (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact VG.Proof.AesGcm.AArch64.frontFrame_work W r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (VG.Proof.AesGcm.AArch64.bodyFrame_work W 0 0 r (mem_bt hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)
  · exact (VG.Proof.AesGcm.AArch64.bodyFrame_work W 0 0 r (mem_ba hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)


theorem saved_omFrame {Ctx W : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact saved_cmp L r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact VG.Proof.AesGcm.AArch64.saved_finFrame L (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact VG.Proof.AesGcm.AArch64.saved_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- What `openMain` writes is above the received tag. -/
theorem omFrame_hi (W : Addr) : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, Region.Sub r ⟨W + BitVec.ofNat 64 16, 2544⟩ := by
  have hi : ∀ d k, 16 ≤ d → d + k ≤ 2560 →
      Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 2544⟩ :=
    fun d k h₁ h₂ => Offset.sub _ h₁ (by omega)
  have st : ∀ d k, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 2544⟩ :=
    fun d k h => Offset.sub_base _ (by omega)
  intro r hr
  simp only [VG.Proof.AesGcm.AArch64.omFrame, VG.Proof.AesGcm.AArch64.frontFrame, j0Frame, absFrame, tFrame, VG.Proof.AesGcm.AArch64.finFrame, tagFrame, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  all_goals first
    | with_reducible exact Region.sub_prefix (by decide)
    | with_reducible exact st _ _ (by decide)
    | with_reducible exact hi _ _ (by decide) (by decide)

/-- The tag compared: 1 in `x27` if it is right, 0 if not. -/
theorem okBit_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block [imm .x27 1, .sub .x .x27 .x27 .x10]) s fun s' =>
      s'.gpr .x27 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Regs [.x27] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `openMain` up to the branch on the tag. -/
def omA (c : Callees) : Prog isa :=
  .seq (j0 c) (.seq (oneAad c) (.seq (.block encPrep) (.seq (decAbs c) (.seq (.block finPrep)
    (.seq (finBody c uO) (.seq (.block [.ldr .x .x28 .x19 tlO]) (.seq cmpSeg
      (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- The rest: the branch on the tag, and the result. -/
def omB (c : Callees) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block []) (oneCrypt c)) (.block [mov .x0 .x27])

theorem Exec.seq_assoc {a b c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a (.seq b c)) s t s') :
    Exec isa (.seq (.seq a b) c) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₂ with
    | seq eb ec => rw [← List.append_assoc]; exact .seq (.seq e₁ eb) ec

theorem Exec.seq_assoc' {a b c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa (.seq (.seq a b) c) s t s') : Exec isa (.seq a (.seq b c)) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => rw [List.append_assoc]; exact .seq ea (.seq eb e₂)

/-- Programs with the same runs. -/
def PEq (c₁ c₂ : Prog isa) : Prop := ∀ s t s', Exec isa c₁ s t s' ↔ Exec isa c₂ s t s'

theorem PEq.assoc (a b c : Prog isa) : VG.Proof.AesGcm.AArch64.PEq (.seq (.seq a b) c) (.seq a (.seq b c)) :=
  fun _ _ _ => ⟨Exec.seq_assoc', Exec.seq_assoc⟩

theorem PEq.seq_right (a : Prog isa) {b b' : Prog isa} (h : VG.Proof.AesGcm.AArch64.PEq b b') : VG.Proof.AesGcm.AArch64.PEq (.seq a b) (.seq a b') := by
  intro s t s'
  constructor
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mp e₂)
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mpr e₂)

theorem PEq.symm {a b : Prog isa} (h : VG.Proof.AesGcm.AArch64.PEq a b) : VG.Proof.AesGcm.AArch64.PEq b a := fun s t s' => (h s t s').symm

theorem PEq.trans {a b c : Prog isa} (h₁ : VG.Proof.AesGcm.AArch64.PEq a b) (h₂ : VG.Proof.AesGcm.AArch64.PEq b c) : VG.Proof.AesGcm.AArch64.PEq a c :=
  fun s t s' => (h₁ s t s').trans (h₂ s t s')

theorem PEq.wp {a b : Prog isa} (h : VG.Proof.AesGcm.AArch64.PEq a b) {s : State} {Q : State → Prop} (w : WP isa b s Q) : WP isa a s Q := by
  obtain ⟨t, s', e, q⟩ := w; exact ⟨t, s', (h _ _ _).mpr e, q⟩

theorem PEq.rel {a b : Prog isa} (h : VG.Proof.AesGcm.AArch64.PEq a b) {P Q : State → State → Prop} (r : RelCT isa P b Q) :
    RelCT isa P a Q := fun _ _ _ _ _ _ hp e₁ e₂ => r _ _ _ _ _ _ hp ((h _ _ _).mp e₁) ((h _ _ _).mp e₂)

/-- `openMain` is `omA` then `omB`. -/
theorem openMain_split (c : Callees) : VG.Proof.AesGcm.AArch64.PEq (.seq (VG.Proof.AesGcm.AArch64.omA c) (VG.Proof.AesGcm.AArch64.omB c)) (openMain c) := by
  unfold VG.Proof.AesGcm.AArch64.omA VG.Proof.AesGcm.AArch64.omB openMain
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

/-- What is known at the branch of `openMain`. -/
structure MidO (Ctx W SP D Np A : Addr) (R nl al n tl : Nat) (s s₇ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₇.mem
  x22 : s₇.gpr .x22 = BitVec.ofNat 64 R
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))

/-- The slots are outside what `openMain` writes before the branch. -/
theorem slots_omFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) :
    ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.AArch64.slots_bodyFrame L ddW r (mem_bt hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using (L.st_w (a := 0) (n := 32) (d := 216) (k := 40) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact VG.Proof.AesGcm.AArch64.slots_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact VG.Proof.AesGcm.AArch64.slots_bodyFrame L ddW r (mem_bt hr)
  · exact VG.Proof.AesGcm.AArch64.slots_bodyFrame L ddW r (mem_ba hr)

theorem openMainA_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (VG.Proof.AesGcm.AArch64.omA v.callees) s (VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s) := by
  unfold VG.Proof.AesGcm.AArch64.omA
  have hle := VG.Proof.AesGcm.AArch64.tagLenOk_le hok
  have hnlt := hdat.ok.lt
  have dD : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (⟨D, n⟩ : Region).Disjoint r := VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.omFrame_work W) ddW
  have dC : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.omFrame_work W) dcW
  have sl := VG.Proof.AesGcm.AArch64.slots_omFrame L ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ VG.Proof.AesGcm.AArch64.omFrame W) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (VG.Proof.AesGcm.AArch64.omFrame W) m m' := fun hs _ _ hf => hf.mono hs
  refine VG.Proof.AesGcm.AArch64.front_ok L v he (fun _ _ => rfl : Kept s.gpr s) h23 h24 h26 h27 hnon haad rfl sA sL sD sN
    fun s₁ h₁ => ?_
  have F₁ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₁.mem :=
    mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) h₁.frame
  have hdat₁ : DataW Ctx (W + BitVec.ofNat 64 16) W s₁ D n := hdat.of_eq h₁.rd h₁.wr
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W SP s₁.gpr R n 0 D (bytesAt s.mem A al) []
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) s₁ :=
    ⟨h₁.env, fun _ _ => rfl, by rw [h₁.x22, h22], hR, h₁.x25, h₁.x26, h₁.x27, h₁.x28, rfl, by decide, hdat₁,
      h₁.hH⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.decAbs_ok L v hB) fun s₂ ⟨he₂, hk₂, x25₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)
  have F₂ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₂.mem :=
    F₁.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) f₂)
  have slot : ∀ {m : Mem}, Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem m → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d h₁ h₂ => VG.Proof.AesGcm.AArch64.slot_kept hf sl h₁ h₂
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.finPrep_ok (al := al) (n := n) he₂.x19 (covers_left he₂.perm.w) (by rw [slot F₂ 224 (by decide) (by decide), sL])
    (by rw [slot F₂ 240 (by decide) (by decide), sN])) fun s₃ ⟨x26₃, x27₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have F₃ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₃.mem := by rw [r₃.mem]; exact F₂
  have hC₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame F₁ dD (by omega)
  have hlen : ([] ++ bytesAt s₁.mem D n).length = n := by rw [List.nil_append, length_bytesAt]
  have x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₃.others _ (by decide), hk₂ .x22 (by decide), h₁.x22, h22]
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame F₃ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.AArch64.finBody_ok L v (.inr rfl) (a := bytesAt s.mem A al)
    (c := [] ++ bytesAt s₁.mem D n)
    (H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)) he₃ (fun _ _ => rfl) x22₃ hR
    (by rw [x26₃, length_bytesAt]) (by rw [x27₃, hlen]) (by rw [hlen]; exact hnlt) hH₃))
    fun s₄ ⟨⟨he₄, hk₄, f₄, out₄⟩, rd₄, wr₄⟩ => ?_)
  have F₄ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₄.mem :=
    F₃.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) f₄)
  obtain ⟨s₅, run₅, x28₅, r₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x28 .x19 tlO] s₄ = some s₅ ∧
      s₅.gpr .x28 = BitVec.ofNat 64 tl ∧ Regs [.x28] s₄ s₅ := by
    have q := he₄.perm.wR (show 248 + 8 ≤ 2560 by decide)
    have e := slot F₄ 248 (by decide) (by decide)
    rw [sT] at e
    refine ⟨_, by arun [he₄.x19, q], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₄.mem.read (W + 248#64) 8 = s₄.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, e]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.of_regs r₅
  refine WP.seq (WP.mono (WP.with_rdwr (cmpSeg_ok L he₅ (fun _ _ => rfl : Kept s₅.gpr s₅) x28₅ hle))
    fun s₆ ⟨⟨x10₆, he₆, hk₆, _, f₆⟩, rd₆, wr₆⟩ => ?_)
  refine WP.mono (VG.Proof.AesGcm.AArch64.okBit_ok (b := decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₅.mem W tl)) (by rw [x10₆]; simp only [decide_eq_true_eq]))
    fun s₇ ⟨x27₇, r₇⟩ => ?_
  have he₇ := he₆.of_regs r₇
  have F₇ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₇.mem := by
    rw [r₇.mem]
    exact F₄.trans (by rw [← r₅.mem]; exact mF (fun r hr => List.mem_append_right _ hr) f₆)
  -- The tag and the comparison.
  have hab : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (ghashInput (bytesAt s.mem A al) ([] ++ bytesAt s₁.mem D n)) := by
    rw [r₃.mem]; exact abs₂ h₁.abs
  have hj₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) =
      Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) := by
    rw [r₃.mem, blockAt_frame f₂ (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact VG.Proof.AesGcm.AArch64.st0_bodyFrame L ddW r (mem_bt hr)
      · exact VG.Proof.AesGcm.AArch64.st0_bodyFrame L ddW r (mem_ba hr)), h₁.j0]
  have hT₅ : bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n) := by
    rw [r₅.mem, out₄ hab, ciph_frame F₃ dC hR, hj₃, Proof.Gcm.fullTag_eq, List.nil_append, hC₁]
  have hW₅ : bytesAt s₅.mem W tl = bytesAt s.mem W tl := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    have := (Offset.disjoint W (d := 0) (n := tl) (e := 16) (k := 2544) (.inl (by omega)) (by omega)
      (by decide)).sub_right (VG.Proof.AesGcm.AArch64.omFrame_hi W r hr)
    simpa using this
  have hb : (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)
        (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT₅, hW₅]
  generalize hBd : decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) = B at x27₇
  have hBeq : decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega)
  have x22₇ : s₇.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₇.others _ (by decide), hk₆ .x22 (by decide), r₅.others _ (by decide), hk₄ .x22 (by decide), x22₃]
  have hcb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
    have d₁ : ∀ r ∈ tFrame (W + BitVec.ofNat 64 16) W 16 ++ absFrame (W + BitVec.ofNat 64 16) W 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · exact (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide))
    have d₂ : ∀ r ∈ VG.Proof.AesGcm.AArch64.finFrame (W + BitVec.ofNat 64 16) W 112,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
    have d₃ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩
    rw [r₇.mem, blockAt_frame f₆ d₃, r₅.mem, blockAt_frame f₄ d₂, r₃.mem, blockAt_frame f₂ d₁, h₁.cb]
  exact ⟨he₇, F₇, x22₇, by rw [x27₇, hBeq],
    hdat.of_eq (by rw [r₇.rd, rd₆, r₅.rd, rd₄, r₃.rd, rd₂, h₁.rd]) (by rw [r₇.wr, wr₆, r₅.wr, wr₄, r₃.wr, wr₂, h₁.wr]),
    by rw [slot F₇ 232 (by decide) (by decide), sD], by rw [slot F₇ 240 (by decide) (by decide), sN], hcb⟩

/-- The loads before `crypt` in `oneCrypt`. -/
theorem ocLdr_ok {Ctx W SP D : Addr} {n : Nat} {s₇ : State} (he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇)
    (sD₇ : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN₇ : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) s₇ fun s₈ =>
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈ := by
  have q₁ := he₇.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₇.perm.wR (show 240 + 8 ≤ 2560 by decide)
  refine WP.run ⟨_, by arun [he₇.x19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD₇]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN₇]; rfl

/-- What `crypt` needs in `oneCrypt`, after its loads. -/
theorem oc_in {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    {s s₇ s₈ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s s₇)
    (h : s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈) :
    CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ :=
  ⟨mo.env.of_regs h.2.2.2, fun _ _ => rfl, by rw [h.2.2.2.others _ (by decide), mo.x22], hR, h.1, h.2.1, h.2.2.1,
    mo.data.of_eq h.2.2.2.rd h.2.2.2.wr⟩

theorem omIte_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (mo : VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s s₇) :
    WP isa (.ite (.zero .x .x27) (.block []) (oneCrypt v.callees)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem D n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else bytesAt s.mem D n := by
  have dD : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (⟨D, n⟩ : Region).Disjoint r := VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.omFrame_work W) ddW
  have dC : ∀ r ∈ VG.Proof.AesGcm.AArch64.omFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.omFrame_work W) dcW
  have hnlt := mo.data.ok.lt
  have F₇ := mo.frame
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega)
  have x27₇ := mo.x27
  generalize decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
    (fun hf => ?_)
  · have hB : B = false := by revert ht; cases B <;> simp
    subst hB
    exact WP.block_nil ⟨mo.env, rfl, Frame.refl _ _, by rw [hD₇]; rfl⟩
  · have hB : B = true := by revert hf; cases B <;> simp
    subst hB
    refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.ocLdr_ok mo.env mo.sD mo.sN) fun s₈ h₈ => ?_)
    have r₈ := h₈.2.2.2
    have F₈ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) s.mem s₈.mem := by rw [r₈.mem]; exact F₇
    have hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
      rw [r₈.mem, mo.cb]
    have hc₈ : ciphOf s₈.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame F₈ dC hR
    have hD₈ : bytesAt s₈.mem D n = bytesAt s.mem D n := bytesAt_frame F₈ dD (by omega)
    refine WP.mono (crypt_ok L v (icb := inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt s.mem Np nl))) (VG.Proof.AesGcm.AArch64.oc_in hR mo h₈)) fun s₉ h₉ => ⟨h₉.env, ?_, by rw [← r₈.mem]; exact h₉.frame, ?_⟩
    · rw [h₉.kept .x27 (by decide), r₈.others _ (by decide)]
    · rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, hD₈, Proof.Gcm.gctr_eq]
      rfl

theorem omB_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (mo : VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s s₇) :
    WP isa (VG.Proof.AesGcm.AArch64.omB v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: VG.Proof.AesGcm.AArch64.omFrame W ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n := by
  unfold VG.Proof.AesGcm.AArch64.omB
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.omIte_ok v L hR ddW dcW mo) fun s₈ ⟨he₈, x27₈, f₈, d₈⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨he₈.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, by simp [gpr_write, x27₈, mo.x27], d₈⟩
  exact (mo.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), fun _ h => h⟩).trans
    (f₈.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), fun _ h => h⟩)

theorem openMain_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMain v.callees) s fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: VG.Proof.AesGcm.AArch64.omFrame W ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n :=
  (VG.Proof.AesGcm.AArch64.openMain_split v.callees).symm.wp (WP.seq (c₁ := VG.Proof.AesGcm.AArch64.omA v.callees) (WP.mono (VG.Proof.AesGcm.AArch64.openMainA_ok v L he h22 hR h23 h24 h26 h27 hnon haad hdat ddW dcW
    sA sL sD sN sT hok) fun _ mo => VG.Proof.AesGcm.AArch64.omB_ok v L hR ddW dcW mo))

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)

/-- What is known after `open`'s entry, from the state `s₀` it was called in, with the
received tag the `tl` bytes at `Tg`. -/
structure OpenIn (Ctx W SP Np A D Tg : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  lay : Lay Ctx (W + BitVec.ofNat 64 16) W
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = BitVec.ofNat 64 tl
  tlt : tl < 2 ^ 64
  non : DataOk (W + BitVec.ofNat 64 16) W s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W s A al
  dat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n
  tagR : Covers [⟨Tg, tl⟩] (s.rd ++ s.wr)
  dnW : (⟨Np, nl⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)
  daW : (⟨A, al⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)
  ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)
  dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)
  dtW : (⟨Tg, tl⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl
  fr : Frame [VG.Proof.AesGcm.AArch64.entryR W, ⟨W, 16⟩] s₀.mem s.mem
  sv : SavedAt s.mem W s₀
  sp₀ : s₀.sp = SP

theorem OpenIn.of_regs {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) (r : Regs [.x9, .x10] s s') :
    VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s' :=
  ⟨o.lay, o.env.of_regs r, by rw [r.others _ (by decide), o.x22], o.rounds, by rw [r.others _ (by decide), o.x23],
    by rw [r.others _ (by decide), o.x24], by rw [r.others _ (by decide), o.x26],
    by rw [r.others _ (by decide), o.x27], by rw [r.others _ (by decide), o.x28], o.tlt,
    o.non.of_eq r.rd r.wr, o.aad.of_eq r.rd r.wr, o.dat.of_eq r.rd r.wr, by rw [r.rd, r.wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [r.mem, o.sA], by rw [r.mem, o.sL], by rw [r.mem, o.sD], by rw [r.mem, o.sN], by rw [r.mem, o.sT],
    by rw [r.mem]; exact o.fr, by rw [r.mem]; exact o.sv, o.sp₀⟩

/-- What the entry and `tagIn` write is in `work`. -/
theorem entry16_work (W : Addr) : ∀ r ∈ [VG.Proof.AesGcm.AArch64.entryR W, ⟨W, 16⟩], Region.Sub r (VG.Proof.AesGcm.AArch64.workR W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Region.sub_prefix (by decide)

/-- `OpenIn` after `tagIn`. -/
theorem OpenIn.tagIn {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) (f : Frame [⟨W, 16⟩] s.mem s'.mem)
    (og : Others loopRegs s s') (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s' := by
  have L := o.lay
  have sl : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    VG.Proof.AesGcm.AArch64.slot_kept f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 216) (n := 40) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)) h₁ h₂
  exact ⟨L, o.env.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
    by rw [og _ (by decide), o.x22], o.rounds, by rw [og _ (by decide), o.x23],
    by rw [og _ (by decide), o.x24], by rw [og _ (by decide), o.x26],
    by rw [og _ (by decide), o.x27], by rw [og _ (by decide), o.x28], o.tlt,
    o.non.of_eq rd wr, o.aad.of_eq rd wr, o.dat.of_eq rd wr, by rw [rd, wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [sl 216 (by decide) (by decide), o.sA], by rw [sl 224 (by decide) (by decide), o.sL],
    by rw [sl 232 (by decide) (by decide), o.sD], by rw [sl 240 (by decide) (by decide), o.sN],
    by rw [sl 248 (by decide) (by decide), o.sT],
    o.fr.trans (f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩),
    o.sv.frame f (saved_tag16 L), o.sp₀⟩

/-- `openPre`'s common arguments. -/
theorem openCore {s : State} (hs : openPre s) : oneCore 3 2 s := by
  simp only [openPre] at hs
  obtain ⟨hrd, hwr, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, -, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩

/-- What `openPre` gives. -/
theorem openLay {s : State} (hs : openPre s) :
    VG.Proof.AesGcm.AArch64.OneLay s 3 2 ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s 2)) := by
  have hs' := hs
  simp only [openPre] at hs'
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dtw, -⟩ := hs'
  exact ⟨VG.Proof.AesGcm.AArch64.oneLay (VG.Proof.AesGcm.AArch64.openCore hs), VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- `open`'s first block: the entry, the tag length and the tag. -/
theorem openEntry_ok {s : State} (hs : openAArch64.pre s) :
    WP isa (.block (oneEntry 16 ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr))) s fun s' =>
      VG.Proof.AesGcm.AArch64.OpenIn (s.gpr .x0) (stackArg s 2) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s' ∧
      s'.gpr .x12 = stackArg s 0 := by
  obtain ⟨ol, tR, dtW⟩ := VG.Proof.AesGcm.AArch64.openLay hs
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have hW16 : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have hT8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (stackArg s 1).toNat := by
    rw [VG.Proof.AesGcm.AArch64.ofNat_toNat']; rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  have hsp16 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := hsp 2 (by decide)
  have hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := hsp 1 (by decide)
  have hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by decide)
  have darg (j : Nat) (hj : j + 8 ≤ 24) : (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg s 2)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 j, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * 3⟩
    rw [show s.sp + BitVec.ofNat 64 (8 * 0) = s.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by omega)
  have h3 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x3)
  have h5 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x5)
  have h7 := VG.Proof.AesGcm.AArch64.ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s 2 = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  generalize htlv : (stackArg s 1).toNat = tl at *
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  have htlt : tl < 2 ^ 64 := htlv ▸ (stackArg s 1).isLt
  refine WP.block_append (WP.mono (VG.Proof.AesGcm.AArch64.entryStash_ok (k := 16) (j := 8) (by decide) (by decide) hW16 hsp16 hsp8 hT8
      (darg 8 (by decide)) hCtx perm)
    fun s₂ ⟨he₂, x22₂, x23₂, x24₂, x26₂, x27₂, x28₂, sl₁, sl₂, sl₃, sl₄, sl₅, f₂, sv₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x12₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesGcm.AArch64.ldrSp_ok (t := .x12) (s := s₂) (k := 0) (by decide)
    (by rw [he₂.sp, f₂.readW (r := ⟨s.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entryR_work W) (darg 0 (by decide))) (by decide), hT0])
    (by rw [rd₂, wr₂, he₂.sp]; exact hsp0)
  refine WP.of_runBlock ⟨s₃, run₃, ?_, x12₃⟩
  rw [hA] at sl₁
  rw [← h5] at sl₂
  rw [hD] at sl₃
  rw [← h7] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (VG.Proof.AesGcm.AArch64.workR W) := Lay.wSub (by decide)
  have g : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28], s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have rd₄ : s₃.rd = s.rd := by rw [rd₃, rd₂]
  have wr₄ : s₃.wr = s.wr := by rw [wr₃, wr₂]
  exact ⟨L, he₂.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)) sp₃ rd₃ wr₃,
    by rw [g .x22 (by simp), x22₂, ← hRR, VG.Proof.AesGcm.AArch64.ofNat_toNat'], by rw [← hRR]; exact hR,
    by rw [g .x23 (by simp), x23₂, hNp], by rw [g .x24 (by simp), x24₂, ← h3], by rw [g .x26 (by simp), x26₂, ← h3],
    by rw [g .x27 (by simp), x27₂], by rw [g .x28 (by simp), x28₂], htlt,
    ⟨by rw [rd₄, wr₄]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩,
    ⟨by rw [rd₄, wr₄]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩,
    ⟨⟨covers_left (by rw [wr₄]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩, by rw [wr₄]; exact dW, dcd⟩,
    by rw [rd₄, wr₄]; exact tR, dnW, daW, ddW, dcW, dtW, by rw [m₃, sl₁], by rw [m₃, sl₂],
    by rw [m₃, sl₃], by rw [m₃, sl₄], by rw [m₃, sl₅],
    by rw [m₃]; exact f₂.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩,
    by rw [m₃]; exact sv₂, rfl⟩

/-- What `openMain` reads, in a state after `tagIn`, as it was on entry. -/
theorem OpenIn.vals {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) :
    ciphOf t.mem Ctx R = ctxCiph s₀.mem Ctx R ∧ blockAt t.mem (Ctx + BitVec.ofNat 64 240) = ctxH s₀.mem Ctx ∧
      bytesAt t.mem Np nl = bytesAt s₀.mem Np nl ∧ bytesAt t.mem A al = bytesAt s₀.mem A al ∧
      bytesAt t.mem D n = bytesAt s₀.mem D n := by
  have hnlt := o.dat.ok.lt
  have hnl := o.non.lt
  have hal := o.aad.lt
  have kE : ∀ {X : Region}, X.Disjoint (VG.Proof.AesGcm.AArch64.workR W) → ∀ r ∈ [VG.Proof.AesGcm.AArch64.entryR W, ⟨W, 16⟩], X.Disjoint r :=
    fun hX => VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entry16_work W) hX
  exact ⟨ciph_frame o.fr (kE o.dcW) o.rounds, blockAt_frame o.fr (kE (o.dcW.sub_left (Lay.ctxSub (by decide)))),
    bytesAt_frame o.fr (kE o.dnW) (by omega), bytesAt_frame o.fr (kE o.daW) (by omega),
    bytesAt_frame o.fr (kE o.ddW) (by omega)⟩

/-- The received tag, after `tagIn`, as it was on entry. -/
theorem OpenIn.tag {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) : bytesAt s.mem Tg tl = bytesAt s₀.mem Tg tl :=
  bytesAt_frame o.fr (VG.Proof.AesGcm.AArch64.keep_of_sub (VG.Proof.AesGcm.AArch64.entry16_work W) o.dtW) (by have := o.tlt; omega)

/-- `open`'s branch on the tag length. -/
theorem oite_ok (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s₃ : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0)) :
    WP isa (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq VG.Impl.AesGcm.AArch64.tagIn (openMain v.callees))) s₃ fun s₄ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ SavedAt s₄.mem W s₀ ∧
      match Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
          (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl) with
      | some pt => (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem D n = pt
      | none => (s₄.gpr .x0).setWidth 32 = 0 ∧ bytesAt s₄.mem D n = bytesAt s₀.mem D n := by
  have L := o.lay
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.ite _ ev (fun ht => ?_) (fun hf => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨o.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, o.sv, ?_⟩
    rw [Spec.Gcm.openResult, ite_eq_right (by simp [hok])]
    exact ⟨by simp [gpr_write], o.vals.2.2.2.2⟩
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := VG.Proof.AesGcm.AArch64.tagLenOk_le hok
    refine WP.seq (WP.mono (tagIn_ok o.env.x19 x12₃ o.x28 hle o.tagR o.env.perm.w
      (o.dtW.sub_right (Region.sub_prefix (by decide)))) fun s₃' ⟨rt, f, og, sp, rd, wr⟩ => ?_)
    have o' := o.tagIn f og sp rd wr
    have hT₃ : bytesAt s₃'.mem W tl = bytesAt s₀.mem Tg tl := by rw [rt, o.tag]
    refine WP.mono (VG.Proof.AesGcm.AArch64.openMain_ok v L o'.env o'.x22 o'.rounds o'.x23 o'.x24 o'.x26 o'.x27 o'.non o'.aad o'.dat
      o'.ddW o'.dcW o'.sA o'.sL o'.sD o'.sN o'.sT hok) fun s₄ hpost => ?_
    dsimp only at hpost
    obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
    refine ⟨he₄, o'.sv.frame F₄ fun r hr => ?_, ?_⟩
    · rcases List.mem_cons.mp hr with h | hr
      · subst h; exact (o.ddW.sub_right (Lay.wSub (by decide))).symm
      rcases List.mem_append.mp hr with hr | hr
      · exact VG.Proof.AesGcm.AArch64.saved_omFrame L r hr
      · exact saved_crFrame L o'.dat r hr
    · obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o'.vals
      rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
      rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
      by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
          (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
      · rw [ite_eq_left hc]
        simp only [hc, decide_true, ite_true] at x0₄ d₄
        exact ⟨by rw [x0₄]; rfl, d₄⟩
      · rw [ite_eq_right hc]
        simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
        exact ⟨by rw [x0₄]; rfl, d₄⟩

theorem open_wp (v : GcmImpl) {s : State} (hs : openAArch64.pre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.openEntry_ok hs) fun s₂ ⟨o₂, x12₂⟩ => ?_)
  refine WP.seq (WP.mono (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.AArch64.oite_ok v (o₂.of_regs r₃) (by rw [r₃.others _ (by decide), x12₂]) x9₃)
    fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  refine WP.mono (exit_ok he₄.x19 (he₄.sp.trans o₂.sp₀.symm) (covers_left he₄.perm.w) sv₄)
    fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  simp only [openAArch64, openRes]
  rw [hm, hx0]
  exact post₄

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis; the bodies by `encBody_rel` and `decBody_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `decAbs` in two runs. -/
theorem decAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decAbs v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  exact VG.Proof.AesGcm.AArch64.padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ =>
    VG.Proof.AesGcm.AArch64.textAbs_rel L v c₁.env c₂.env c₁.kept c₂.kept c₁.x23 c₂.x23 c₁.x24 c₂.x24 c₁.x25 c₂.x25
      ((c₁.kept .x26 (by decide)).trans k26₁) ((c₂.kept .x26 (by decide)).trans k26₂) c₁.data.ok c₂.data.ok

/-- `decBody` in two runs. -/
theorem decBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decBody v.callees) TT := by
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (h₁.kept .x22 (by decide)).symm.trans h₁.x22
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (h₂.kept .x22 (by decide)).symm.trans h₂.x22
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine rel_seq (VG.Proof.AesGcm.AArch64.decAbs_rel L v h₁ h₂ hq) (VG.Proof.AesGcm.AArch64.decAbs_ok L v h₁) (VG.Proof.AesGcm.AArch64.decAbs_ok L v h₂)
    fun τ₁ τ₂ ⟨e₁, kk₁, x25₁, _, rd₁, wr₁, _⟩ ⟨e₂, kk₂, x25₂, _, rd₂, wr₂, _⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [e₁.sp, e₂.sp])
      (by agree_tac [kk₁ .x26 (by decide), kk₂ .x26 (by decide), kk₁ .x28 (by decide),
        kk₂ .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok kk₁ k26₁ k28₁) (textPiece_ok kk₂ k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := kk₁.of_others rp₁.others
  have pk₂ := kk₂.of_others rp₂.others
  exact VG.Proof.AesGcm.AArch64.crypt_rel L v
    ⟨e₁.of_regs rp₁, pk₁, (pk₁ .x22 (by decide)).trans k22₁, h₁.rounds, p23₁, p24₁,
      by rw [rp₁.others _ (by decide), x25₁], h₁.data.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁])⟩
    ⟨e₂.of_regs rp₂, pk₂, (pk₂ .x22 (by decide)).trans k22₂, h₂.rounds, p23₂, p24₂,
      by rw [rp₂.others _ (by decide), x25₂], h₂.data.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂])⟩

end

/-- The entry, a body and the exit, in two runs. -/
theorem cr_rel {body : Prog isa} {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂)
    (hq : streamCryptPub σ₁ σ₂)
    (hrel : ∀ {Ctx St W SP : Addr} {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
      {H₁ H₂ : Block} {τ₁ τ₂ : State}, Lay Ctx St W → BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ τ₁ →
      BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ τ₂ → a₁.length % 16 = a₂.length % 16 →
      RelCT isa (Eq2 τ₁ τ₂) body TT)
    (hw : ∀ {Ctx St W SP : Addr} {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
      {τ : State}, Lay Ctx St W → BodyIn Ctx St W SP k R n P D a c H τ →
      WP isa body τ fun τ' => Env Ctx St W SP τ') :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block crEntry) (.seq body (.block restore))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩ := hq
  simp only [streamCryptPre] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q5, ← q6, ← q7] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcd, dcw, dsd, dsw, ddw, wc, ws, wd, ww, hR⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x2 = St at *
  generalize hD : σ₁.gpr .x5 = D at *
  generalize hn : (σ₁.gpr .x6).toNat = n at *
  generalize hW : σ₁.gpr .x7 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x6).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) (hR : rounds (σ.gpr .x1))
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x22 = BitVec.ofNat 64 (σ.gpr .x1).toNat ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x3).toNat % 16) ∧ σ'.gpr .x26 = BitVec.ofNat 64 n ∧
        σ'.gpr .x27 = BitVec.ofNat 64 (σ.gpr .x4).toNat ∧ σ'.gpr .x28 = D ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      BodyIn Ctx St W σ.sp σ'.gpr (σ.gpr .x1).toNat n (σ.gpr .x4).toNat D
        (Spec.Gcm.zeros ((σ.gpr .x3).toNat % 16)) (Spec.Gcm.zeros (σ.gpr .x4).toNat)
        (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) σ' := by
    obtain ⟨he, hk, x22, x25, x26, x27, x28, _, rd, wr⟩ := h
    exact ⟨he, hk, x22, hR, by rw [x25, VG.Proof.AesGcm.AArch64.hz_mod _ (Nat.mod_lt _ (by decide))], x26, x27, x28,
      Proof.Gcm.length_zeros _, (σ.gpr .x4).isLt,
      ⟨⟨covers_left (by rw [wr, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
        by rw [wr, hwr]; exact covers_of_mem (by simp), dcd⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, q1, ← q2, q3, q4, ← q5, q6, ← q7]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.crEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (VG.Proof.AesGcm.AArch64.crEntry_ok q0.symm q2.symm q5.symm (by rw [← q6, hn]) q7.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have b₁ := mk σ₁ τ₁ hwr₁ hR a₁
  have b₂ := mk σ₂ τ₂ hwr₂ (by rw [← q1]; exact hR) a₂
  rw [← qsp, ← q1, ← q4] at b₂
  refine rel_seq (hrel L b₁ b₂ (by rw [Proof.Gcm.length_zeros, Proof.Gcm.length_zeros, Nat.mod_mod, Nat.mod_mod, q3]))
    (hw L b₁) (hw L b₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa streamEncryptAArch64.pre streamEncryptAArch64.pub (streamEncrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => VG.Proof.AesGcm.AArch64.cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => VG.Proof.AesGcm.AArch64.encBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (encBody_ok L v b 0) fun _ h => h.env)

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa streamDecryptAArch64.pre streamDecryptAArch64.pub (streamDecrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => VG.Proof.AesGcm.AArch64.cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => VG.Proof.AesGcm.AArch64.decBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (decBody_ok L v b 0) fun _ h => h.env)

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.OneCT`. -/
section

/-!
# AES-GCM on AArch64: what `seal` and `open` share, in two runs

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load (`RelCT.block_split`), and the rest runs from
`x9`, which holds `work` (public) in both runs. Then `j0`, `oneAad` and
`encPrep` (`front_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Two runs of `a; (b; c)` are two runs of `(a; b); c`. -/
theorem RelCT.assoc {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc e₁) (Exec.seq_assoc e₂)

theorem RelCT.assoc' {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc' e₁) (Exec.seq_assoc' e₂)

/-- `oneAad`'s first block. -/
theorem aadBlk_ok {s : State} {W A : Addr} {al : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) s fun s' =>
      s'.gpr .x23 = A ∧ s'.gpr .x24 = BitVec.ofNat 64 al ∧ s'.gpr .x25 = BitVec.ofNat 64 0 ∧
      Regs [.x23, .x24, .x25] s s' := by
  have q₁ := in_off hr (show 216 + 8 ≤ 2560 by decide) (by decide)
  have q₂ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sA]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sL]; rfl

/-- `encPrep`. -/
theorem encPrep_ok {s : State} {W D : Addr} {al n : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hlt : al < 2 ^ 64)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block encPrep) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧ s'.gpr .x27 = 0 ∧
      s'.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s s' := by
  have q₂ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  have q₃ := in_off hr (show 232 + 8 ≤ 2560 by decide) (by decide)
  have q₄ := in_off hr (show 240 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by simp only [encPrep]; arun [h19, q₂, q₃, q₄], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL,
      show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD]

/-- What `front_ok` needs of a run. -/
structure FrontIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (Np A D : Addr) (nl al n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  non : DataOk St W s Np nl
  aad : DataOk St W s A al
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- What `front_rel` leaves of a run. -/
structure FrontOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (D : Addr) (al n : Nat) (s₀ s : State) :
    Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = k .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (al % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  frame : Frame (VG.Proof.AesGcm.AArch64.frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `j0`, `oneAad` and `encPrep` in two runs. -/
theorem front_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {Np A D : Addr} {nl al n : Nat} {σ₁ σ₂ : State}
    (h₁ : VG.Proof.AesGcm.AArch64.FrontIn Ctx St W SP k₁ Np A D nl al n σ₁) (h₂ : VG.Proof.AesGcm.AArch64.FrontIn Ctx St W SP k₂ Np A D nl al n σ₂)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, VG.Proof.AesGcm.AArch64.FrontOut Ctx St W SP k₁ D al n σ₁ τ₁ → VG.Proof.AesGcm.AArch64.FrontOut Ctx St W SP k₂ D al n σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) TT := by
  have hlt := h₁.aad.lt
  have j₁ : J0In Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₁ :=
    ⟨h₁.env, h₁.kept, h₁.x23, h₁.x24, h₁.x26, h₁.x27, h₁.non, rfl⟩
  have j₂ : J0In Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₂ :=
    ⟨h₂.env, h₂.kept, h₂.x23, h₂.x24, h₂.x26, h₂.x27, h₂.non, rfl⟩
  refine rel_seq (VG.Proof.AesGcm.AArch64.j0_rel L v j₁ j₂) (WP.with_rdwr (j0_ok L v j₁)) (WP.with_rdwr (j0_ok L v j₂))
    fun s₁ s₂ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have sl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => VG.Proof.AesGcm.AArch64.slot_kept o₁.frame (VG.Proof.AesGcm.AArch64.slots_j0Frame L) a b
  have sl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => VG.Proof.AesGcm.AArch64.slot_kept o₂.frame (VG.Proof.AesGcm.AArch64.slots_j0Frame L) a b
  refine RelCT.assoc' ?_
  refine rel_seq (rel_taint [.x19] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.env.x19, o₂.env.x19])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.aadBlk_ok (A := A) (al := al) o₁.env.x19 (covers_left o₁.env.perm.w) (by rw [sl₁ 216 (by decide) (by decide), h₁.sA])
      (by rw [sl₁ 224 (by decide) (by decide), h₁.sL]))
    (VG.Proof.AesGcm.AArch64.aadBlk_ok (A := A) (al := al) o₂.env.x19 (covers_left o₂.env.perm.w) (by rw [sl₂ 216 (by decide) (by decide), h₂.sA])
      (by rw [sl₂ 224 (by decide) (by decide), h₂.sL]))
    fun s₁' s₂' ⟨x23₁, x24₁, x25₁, r₁⟩ ⟨x23₂, x24₂, x25₂, r₂⟩ => ?_
  have a₁ : AbsIn Ctx St W SP k₁ (blockAt s₁'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₁' :=
    ⟨o₁.env.of_regs r₁, o₁.kept.of_others r₁.others, x23₁, x24₁, x25₁, rfl,
      h₁.aad.of_eq (by rw [r₁.rd, rd₁]) (by rw [r₁.wr, wr₁]), rfl⟩
  have a₂ : AbsIn Ctx St W SP k₂ (blockAt s₂'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₂' :=
    ⟨o₂.env.of_regs r₂, o₂.kept.of_others r₂.others, x23₂, x24₂, x25₂, rfl,
      h₂.aad.of_eq (by rw [r₂.rd, rd₂]) (by rw [r₂.wr, wr₂]), rfl⟩
  refine rel_seq (VG.Proof.AesGcm.AArch64.absorb_rel L v (.inr rfl) a₁ a₂) (WP.with_rdwr (absorb_ok L (.inr rfl) v a₁))
    (WP.with_rdwr (absorb_ok L (.inr rfl) v a₂)) fun t₁ t₂ ⟨b₁, brd₁, bwr₁⟩ ⟨b₂, brd₂, bwr₂⟩ => ?_
  have f₁ : Frame (VG.Proof.AesGcm.AArch64.frontFrame St W) σ₁.mem t₁.mem :=
    (o₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₁.mem]; exact b₁.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have f₂ : Frame (VG.Proof.AesGcm.AArch64.frontFrame St W) σ₂.mem t₂.mem :=
    (o₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact b₂.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have tl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => VG.Proof.AesGcm.AArch64.slot_kept f₁ (VG.Proof.AesGcm.AArch64.slots_frontFrame L) a b
  have tl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => VG.Proof.AesGcm.AArch64.slot_kept f₂ (VG.Proof.AesGcm.AArch64.slots_frontFrame L) a b
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.encPrep_ok (D := D) (n := n) b₁.env.x19 (covers_left b₁.env.perm.w) hlt (by rw [tl₁ 224 (by decide) (by decide), h₁.sL])
      (by rw [tl₁ 232 (by decide) (by decide), h₁.sD]) (by rw [tl₁ 240 (by decide) (by decide), h₁.sN]))
    (VG.Proof.AesGcm.AArch64.encPrep_ok (D := D) (n := n) b₂.env.x19 (covers_left b₂.env.perm.w) hlt (by rw [tl₂ 224 (by decide) (by decide), h₂.sL])
      (by rw [tl₂ 232 (by decide) (by decide), h₂.sD]) (by rw [tl₂ 240 (by decide) (by decide), h₂.sN]))
    fun u₁ u₂ ⟨e25₁, e26₁, e27₁, e28₁, er₁⟩ ⟨e25₂, e26₂, e27₂, e28₂, er₂⟩ => ?_
  refine hr u₁ u₂ ⟨b₁.env.of_regs er₁, ?_, e25₁, e26₁, e27₁, e28₁, by rw [er₁.mem]; exact f₁,
      by rw [er₁.rd, brd₁, r₁.rd, rd₁], by rw [er₁.wr, bwr₁, r₁.wr, wr₁]⟩
    ⟨b₂.env.of_regs er₂, ?_, e25₂, e26₂, e27₂, e28₂, by rw [er₂.mem]; exact f₂,
      by rw [er₂.rd, brd₂, r₂.rd, rd₂], by rw [er₂.wr, bwr₂, r₂.wr, wr₂]⟩
  · rw [er₁.others _ (by decide), b₁.kept .x22 (by decide)]
  · rw [er₂.others _ (by decide), b₂.kept .x22 (by decide)]

end


/-- The load of `work`, at `sp + k`. -/
theorem ldr9_ok {s : State} {W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp .x9 k]) s fun s' => s'.gpr .x9 = W ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  let ⟨s', run, x9, g, sp, _, rd, wr⟩ := VG.Proof.AesGcm.AArch64.ldrSp_ok hk hW hsp
  WP.of_runBlock ⟨s', run, x9, g, sp, rd, wr⟩

/-- The entry of `seal` and `open` in two runs, with `work` at `sp + k`. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} {k : Nat} (hk : k = 8 ∨ k = 16)
    (hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = W) (hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (hw₁ : Covers [⟨W, 2560⟩] σ₁.wr) (hw₂ : Covers [⟨W, 2560⟩] σ₂.wr) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k)) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl <;> decide
  have run : ∀ {σ : State}, σ.mem.readW (σ.sp + BitVec.ofNat 64 k) 64 = W →
      InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 k) 8 → Covers [⟨W, 2560⟩] σ.wr →
      WP isa (.block ([.ldrSp .x9 k] ++ save .x9)) σ fun s' => s'.gpr .x9 = W ∧
        (∀ r, r ≠ .x9 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun hW hsp hw =>
    WP.block_append (WP.mono (VG.Proof.AesGcm.AArch64.ldr9_ok hk' hW hsp) fun s₁ ⟨x9₁, g₁, sp₁, rd₁, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact hw)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], fun r hr => by rw [g₂, g₁ r hr], by rw [sp₂, sp₁]⟩)
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 k]) h).isSome = true := by
    rcases hk with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x9]) (.block (save .x9)) h).isSome = true := ⟨_, by taint_decide⟩
  show RelCT isa _ (.block ([.ldrSp .x9 k] ++ save .x9 ++ _)) _
  refine RelCT.block_split (rel_seq (RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) t₁)
      (VG.Proof.AesGcm.AArch64.ldr9_ok hk' hW₁ hsp₁) (VG.Proof.AesGcm.AArch64.ldr9_ok hk' hW₂ hsp₂)
      fun τ₁ τ₂ ⟨x9₁, _, sp₁, _, _⟩ ⟨x9₂, _, sp₂, _, _⟩ =>
        rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) t₂))
    (run hW₁ hsp₁ hw₁) (run hW₂ hsp₂ hw₂) fun τ₁ τ₂ ⟨x9₁, g₁, sp₁⟩ ⟨x9₂, g₂, sp₂⟩ => ?_)
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_ ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  · rw [g₁ r h9, g₂ r h9]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.SealCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry by `entry_rel`,
`j0` and the additional data by `front_rel`, the text by `encBody_rel` and
the tag by `finBody_rel`; the blocks between them by the taint analysis, with
`tag`, which the code loads from memory, public in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `oneCore` gives, with the values of the first run. -/
structure OneFacts (σ σ₀ : State) (n w : Nat) : Prop where
  ol : VG.Proof.AesGcm.AArch64.OneLay σ₀ n w
  hW : stackArg σ w = stackArg σ₀ w
  perm : Perm (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ
  hsp : ∀ i < n, InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 (8 * i)) 8
  nonceR : Covers [⟨σ₀.gpr .x2, (σ₀.gpr .x3).toNat⟩] (σ.rd ++ σ.wr)
  aadR : Covers [⟨σ₀.gpr .x4, (σ₀.gpr .x5).toNat⟩] (σ.rd ++ σ.wr)
  dataW : Covers [⟨σ₀.gpr .x6, (σ₀.gpr .x7).toNat⟩] σ.wr
  args : (args σ n).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg σ₀ w))

theorem oneFacts {σ₁ σ₂ : State} {n w : Nat} (hw : w < n) (h₁ : oneCore n w σ₁) (h₂ : oneCore n w σ₂)
    (hq : onePub n σ₁ σ₂) : VG.Proof.AesGcm.AArch64.OneFacts σ₁ σ₁ n w ∧ VG.Proof.AesGcm.AArch64.OneFacts σ₂ σ₁ n w := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qw : stackArg σ₁ w = stackArg σ₂ w := qa w hw
  have o₁ := VG.Proof.AesGcm.AArch64.oneLay h₁
  have o₂ := VG.Proof.AesGcm.AArch64.oneLay h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW, o₁.args⟩,
    ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q2, ← q3] at this; exact this
  · have := o₂.aadR; rw [← q4, ← q5] at this; exact this
  · have := o₂.dataW; rw [← q6, ← q7] at this; exact this
  · have := o₂.args; rw [← qw] at this; exact this

/-- A stack argument, at `sp + j` with `j < 8 * n`, is outside `work`. -/
theorem OneFacts.argW {σ σ₀ : State} {n w : Nat} (f : VG.Proof.AesGcm.AArch64.OneFacts σ σ₀ n w) {j : Nat} (hj : j + 8 ≤ 8 * n) :
    (⟨σ.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR (stackArg σ₀ w)) := by
  refine f.args.sub_left ?_
  show Region.Sub ⟨σ.sp + BitVec.ofNat 64 j, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * n⟩
  rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
  exact Offset.sub_base _ hj

/-- `FrontIn` after the entry. -/
theorem frontIn_of {σ σ₀ τ : State} {n w : Nat} {V : BitVec 64} (f : VG.Proof.AesGcm.AArch64.OneFacts σ σ₀ n w)
    (h3 : σ.gpr .x3 = σ₀.gpr .x3) (h2 : σ.gpr .x2 = σ₀.gpr .x2) (h4 : σ.gpr .x4 = σ₀.gpr .x4)
    (h5 : σ.gpr .x5 = σ₀.gpr .x5) (h6 : σ.gpr .x6 = σ₀.gpr .x6) (h7 : σ.gpr .x7 = σ₀.gpr .x7)
    (a : Env (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ ∧
      τ.gpr .x22 = σ.gpr .x1 ∧ τ.gpr .x23 = σ.gpr .x2 ∧ τ.gpr .x24 = σ.gpr .x3 ∧
      τ.gpr .x26 = σ.gpr .x3 ∧ τ.gpr .x27 = 0 ∧ τ.gpr .x28 = V ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 216) 64 = σ.gpr .x4 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 224) 64 = σ.gpr .x5 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 232) 64 = σ.gpr .x6 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 240) 64 = σ.gpr .x7 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 248) 64 = V ∧
      Frame [VG.Proof.AesGcm.AArch64.entryR (stackArg σ₀ w)] σ.mem τ.mem ∧ SavedAt τ.mem (stackArg σ₀ w) σ ∧ τ.rd = σ.rd ∧
      τ.wr = σ.wr) :
    VG.Proof.AesGcm.AArch64.FrontIn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ.gpr (σ₀.gpr .x2)
      (σ₀.gpr .x4) (σ₀.gpr .x6) (σ₀.gpr .x3).toNat (σ₀.gpr .x5).toNat (σ₀.gpr .x7).toNat τ := by
  obtain ⟨he, _, x23, x24, x26, x27, _, s1, s2, s3, s4, _, _, _, rd, wr⟩ := a
  have sub16 : Region.Sub ⟨stackArg σ₀ w + BitVec.ofNat 64 16, 80⟩ (VG.Proof.AesGcm.AArch64.workR (stackArg σ₀ w)) := Lay.wSub (by decide)
  exact ⟨he, fun _ _ => rfl, by rw [x23, h2], by rw [x24, h3, VG.Proof.AesGcm.AArch64.ofNat_toNat'], by rw [x26, h3, VG.Proof.AesGcm.AArch64.ofNat_toNat'], x27,
    ⟨by rw [rd, wr]; exact f.nonceR, (σ₀.gpr .x3).isLt, f.ol.nw, f.ol.nonce.sub_right sub16, f.ol.nonce⟩,
    ⟨by rw [rd, wr]; exact f.aadR, (σ₀.gpr .x5).isLt, f.ol.aw, f.ol.aad.sub_right sub16, f.ol.aad⟩,
    by rw [s1, h4], by rw [s2, h5, VG.Proof.AesGcm.AArch64.ofNat_toNat'], by rw [s3, h6], by rw [s4, h7, VG.Proof.AesGcm.AArch64.ofNat_toNat']⟩

/-- The entry of `seal` and `open` and its stash, in two runs: `work` at `sp + k`, and
the stack argument at `sp + j` kept. -/
theorem entryStash_rel {σ₁ σ₂ : State} {n w k j : Nat} (hk : k = 8 ∨ k = 16) (hkw : k = 8 * w) (hj : j = 0 ∨ j = 8)
    (f₁ : VG.Proof.AesGcm.AArch64.OneFacts σ₁ σ₁ n w) (f₂ : VG.Proof.AesGcm.AArch64.OneFacts σ₂ σ₁ n w) (hwn : w < n) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k ++ stashArg j)) TT := by
  subst hkw
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := f₂.hW
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block (stashArg j)) h).isSome = true := by
    rcases hj with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine RelCT.block_split (rel_seq (VG.Proof.AesGcm.AArch64.entry_rel hk hW₁ hW₂ (f₁.hsp w hwn) (f₂.hsp w hwn) f₁.perm.w f₂.perm.w qsp hq)
    (VG.Proof.AesGcm.AArch64.oneEntry_ok (by rcases hk with h | h <;> rw [h] <;> decide) hW₁ (f₁.hsp w hwn) rfl f₁.perm)
    (VG.Proof.AesGcm.AArch64.oneEntry_ok (by rcases hk with h | h <;> rw [h] <;> decide) hW₂ (f₂.hsp w hwn) (hq .x0 (by simp)).symm f₂.perm)
    fun τ₁ τ₂ a₁ a₂ => rel_taint [.x19] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac [a₁.1.x19, a₂.1.x19]) ts)

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨f₁, f₂⟩ := VG.Proof.AesGcm.AArch64.oneFacts (by decide : 1 < 2) (VG.Proof.AesGcm.AArch64.sealCore h₁) (VG.Proof.AesGcm.AArch64.sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have L := f₁.ol.lay
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := qt.symm
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := f₂.hW
  refine rel_seq (VG.Proof.AesGcm.AArch64.entryStash_rel (k := 8) (j := 0) (.inl rfl) rfl (.inl rfl) f₁ f₂ (by decide) qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (VG.Proof.AesGcm.AArch64.entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₁ (f₁.hsp 1 (by decide)) (f₁.hsp 0 (by decide))
      hT₁ (f₁.argW (by decide)) rfl f₁.perm)
    (VG.Proof.AesGcm.AArch64.entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₂ (f₂.hsp 1 (by decide)) (f₂.hsp 0 (by decide))
      hT₂ (f₂.argW (by decide)) q0.symm f₂.perm) fun τ₁ τ₂ a₁ a₂ => ?_
  have i₁ := VG.Proof.AesGcm.AArch64.frontIn_of f₁ rfl rfl rfl rfl rfl rfl a₁
  have i₂ := VG.Proof.AesGcm.AArch64.frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm a₂
  rw [← qsp] at i₂
  obtain ⟨_, x22₁, _, _, _, _, _, _, s2₁, _, s4₁, s5₁, _, _, rd₁, wr₁⟩ := a₁
  obtain ⟨_, x22₂, _, _, _, _, _, _, s2₂, _, s4₂, s5₂, _, _, rd₂, wr₂⟩ := a₂
  rw [← q1] at x22₂
  rw [← q5] at s2₂
  rw [← q7] at s4₂
  have ol := f₁.ol
  have sub16 : Region.Sub ⟨stackArg σ₁ 1 + BitVec.ofNat 64 16, 80⟩ (VG.Proof.AesGcm.AArch64.workR (stackArg σ₁ 1)) := Lay.wSub (by decide)
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := ol.rounds
  have hal := (σ₁.gpr .x5).isLt
  have hn := (σ₁.gpr .x7).isLt
  refine VG.Proof.AesGcm.AArch64.front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  have mkB : ∀ {σ τ u : State}, VG.Proof.AesGcm.AArch64.OneFacts σ σ₁ 2 1 → τ.gpr .x22 = σ₁.gpr .x1 → τ.wr = σ.wr →
      VG.Proof.AesGcm.AArch64.FrontOut (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp u.gpr (σ₁.gpr .x1).toNat
        (σ₁.gpr .x7).toNat 0 (σ₁.gpr .x6) (Spec.Gcm.zeros (σ₁.gpr .x5).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f x22 wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x22, x22, VG.Proof.AesGcm.AArch64.ofNat_toNat'], hRb, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd⟩, rfl⟩
  have B₁ := mkB f₁ x22₁ wr₁ o₁
  have B₂ := mkB f₂ x22₂ wr₂ o₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  have sl : ∀ {σ τ u w : State}, VG.Proof.AesGcm.AArch64.OneFacts σ σ₁ 2 1 →
      VG.Proof.AesGcm.AArch64.FrontOut (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      Frame (bodyFrame (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        u.mem w.mem → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      w.mem.readW (stackArg σ₁ 1 + BitVec.ofNat 64 d) 64 = τ.mem.readW (stackArg σ₁ 1 + BitVec.ofNat 64 d) 64 :=
    fun _ o fb d h₁ h₂ => by
      rw [VG.Proof.AesGcm.AArch64.slot_kept fb (VG.Proof.AesGcm.AArch64.slots_bodyFrame L ol.data) h₁ h₂, VG.Proof.AesGcm.AArch64.slot_kept o.frame (VG.Proof.AesGcm.AArch64.slots_frontFrame L) h₁ h₂]
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₁.env.x19 (covers_left b₁.env.perm.w) (by rw [sl f₁ o₁ b₁.frame 224 (by decide) (by decide), s2₁,
                              VG.Proof.AesGcm.AArch64.ofNat_toNat']) (by rw [sl f₁ o₁ b₁.frame 240 (by decide) (by decide), s4₁, VG.Proof.AesGcm.AArch64.ofNat_toNat']))
    (VG.Proof.AesGcm.AArch64.finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₂.env.x19 (covers_left b₂.env.perm.w) (by rw [sl f₂ o₂ b₂.frame 224 (by decide) (by decide), s2₂,
                              VG.Proof.AesGcm.AArch64.ofNat_toNat']) (by rw [sl f₂ o₂ b₂.frame 240 (by decide) (by decide), s4₂, VG.Proof.AesGcm.AArch64.ofNat_toNat']))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  refine rel_seq (rel_taint [.x19] (by rw [r₁.sp, r₂.sp, b₁.env.sp, b₂.env.sp])
      (by agree_tac [r₁.others .x19 (by decide), r₂.others .x19 (by decide), b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.ldr28_ok (V := stackArg σ₁ 0) (b₁.env.of_regs r₁) (by rw [r₁.mem, sl f₁ o₁ b₁.frame 248 (by decide) (by decide), s5₁]))
    (VG.Proof.AesGcm.AArch64.ldr28_ok (V := stackArg σ₁ 0) (b₂.env.of_regs r₂) (by rw [r₂.mem, sl f₂ o₂ b₂.frame 248 (by decide) (by decide), s5₂]))
    fun z₁' z₂' ⟨x28₁, r₁'⟩ ⟨x28₂, r₂'⟩ => ?_
  have y22₁ : z₁'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₁'.others _ (by decide), r₁.others _ (by decide), b₁.kept .x22 (by decide), o₁.x22, x22₁, VG.Proof.AesGcm.AArch64.ofNat_toNat']
  have y22₂ : z₂'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₂'.others _ (by decide), r₂.others _ (by decide), b₂.kept .x22 (by decide), o₂.x22, x22₂, VG.Proof.AesGcm.AArch64.ofNat_toNat']
  have e₁ := (b₁.env.of_regs r₁).of_regs r₁'
  have e₂ := (b₂.env.of_regs r₂).of_regs r₂'
  have y26₁ : z₁'.gpr .x26 = _ := (r₁'.others .x26 (by decide)).trans x26₁
  have y26₂ : z₂'.gpr .x26 = _ := (r₂'.others .x26 (by decide)).trans x26₂
  have y27₁ : z₁'.gpr .x27 = _ := (r₁'.others .x27 (by decide)).trans x27₁
  have y27₂ : z₂'.gpr .x27 = _ := (r₂'.others .x27 (by decide)).trans x27₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.finBody_rel L v (.inl rfl) e₁ e₂ (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ hRb y26₁ y26₂ y27₁ y27₂ hal hn)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inl rfl) e₁ (fun _ _ => rfl) y22₁ hRb y26₁ y27₁ hn)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inl rfl) e₂ (fun _ _ => rfl) y22₂ hRb y26₂ y27₂ hn) fun g₁ g₂ h₁ h₂ => ?_
  have c28₁ : g₁.gpr .x28 = stackArg σ₁ 0 := (h₁.2.1 .x28 (by decide)).trans x28₁
  have c28₂ : g₂.gpr .x28 = stackArg σ₁ 0 := (h₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [h₁.1.sp, h₂.1.sp])
    (by agree_tac [h₁.1.x19, h₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open` leaks only whether the tag is right

Untrusted: everything here is checked by Lean. As for `seal` (`SealCT.lean`),
with the received tag copied in and compared, and the text decrypted, by
`decAbs_rel` and the taint analysis. The branches on the tag length and on the comparison are public:
the tag length is an argument, and whether the tag is right is what
`openAArch64.pub` leaks.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- The bit `openMain` computes, after `tagIn`, is whether `open` succeeds. -/
theorem tagBit {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) (rt : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt t.mem Np nl) (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) =
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome := by
  obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
  rw [hc₃, hH₃, hN₃, hA₃, hD₃, rt, Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
  · rw [ite_eq_left hc]; simp [hc]
  · rw [ite_eq_right hc]; simp [hc]

/-- `FrontIn` from `OpenIn`. -/
theorem OpenIn.front {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) :
    VG.Proof.AesGcm.AArch64.FrontIn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr Np A D nl al n t :=
  ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, o.aad, o.sA, o.sL, o.sD, o.sN⟩

/-- `openMain` up to the branch on the tag, in two runs. -/
theorem omA_rel (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₁ s₂ t₁ t₂ : State}
    (o₁ : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₁ t₁) (o₂ : VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s₂ t₂) :
    RelCT isa (Eq2 t₁ t₂) (VG.Proof.AesGcm.AArch64.omA v.callees) TT := by
  have L := o₁.lay
  have hal := o₁.aad.lt
  have hn := o₁.dat.ok.lt
  have sl := VG.Proof.AesGcm.AArch64.slots_omFrame L o₁.ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ VG.Proof.AesGcm.AArch64.omFrame W) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (VG.Proof.AesGcm.AArch64.omFrame W) m m' := fun hs _ _ hf => hf.mono hs
  unfold VG.Proof.AesGcm.AArch64.omA
  refine VG.Proof.AesGcm.AArch64.front_rel L v o₁.front o₂.front fun u₁ u₂ p₁ p₂ => ?_
  have mkB : ∀ {s t u : State}, VG.Proof.AesGcm.AArch64.OpenIn Ctx W SP Np A D Tg R nl al n tl s t →
      VG.Proof.AesGcm.AArch64.FrontOut Ctx (W + BitVec.ofNat 64 16) W SP t.gpr D al n t u →
      BodyIn Ctx (W + BitVec.ofNat 64 16) W SP u.gpr R n 0 D (Spec.Gcm.zeros al) []
        (blockAt u.mem (Ctx + BitVec.ofNat 64 240)) u := fun o p =>
    ⟨p.env, fun _ _ => rfl, by rw [p.x22, o.x22], o.rounds, by rw [p.x25, Proof.Gcm.length_zeros],
      p.x26, p.x27, p.x28, rfl, by decide, o.dat.of_eq (by rw [p.rd]) (by rw [p.wr]), rfl⟩
  have B₁ := mkB o₁ p₁
  have B₂ := mkB o₂ p₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.decAbs_rel L v B₁ B₂ rfl) (VG.Proof.AesGcm.AArch64.decAbs_ok L v B₁) (VG.Proof.AesGcm.AArch64.decAbs_ok L v B₂)
    fun w₁ w₂ ⟨e₁, kk₁, _, fr₁, _, _, _⟩ ⟨e₂, kk₂, _, fr₂, _, _, _⟩ => ?_
  have F₁ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) t₁.mem w₁.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₁.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₁)
  have F₂ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) t₂.mem w₂.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₂.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₂)
  refine rel_seq (rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.finPrep_ok (al := al) (n := n) e₁.x19 (covers_left e₁.perm.w)
      (by rw [VG.Proof.AesGcm.AArch64.slot_kept F₁ sl (by decide) (by decide), o₁.sL]) (by rw [VG.Proof.AesGcm.AArch64.slot_kept F₁ sl (by decide) (by decide), o₁.sN]))
    (VG.Proof.AesGcm.AArch64.finPrep_ok (al := al) (n := n) e₂.x19 (covers_left e₂.perm.w)
      (by rw [VG.Proof.AesGcm.AArch64.slot_kept F₂ sl (by decide) (by decide), o₂.sL]) (by rw [VG.Proof.AesGcm.AArch64.slot_kept F₂ sl (by decide) (by decide), o₂.sN]))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  have y22₁ : z₁.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₁.others _ (by decide), kk₁ .x22 (by decide), p₁.x22, o₁.x22]
  have y22₂ : z₂.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₂.others _ (by decide), kk₂ .x22 (by decide), p₂.x22, o₂.x22]
  refine rel_seq (VG.Proof.AesGcm.AArch64.finBody_rel L v (.inr rfl) (e₁.of_regs r₁) (e₂.of_regs r₂) (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ o₁.rounds x26₁ x26₂ x27₁ x27₂ hal hn)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inr rfl) (e₁.of_regs r₁) (fun _ _ => rfl) y22₁ o₁.rounds x26₁ x27₁ hn)
    (VG.Proof.AesGcm.AArch64.finBody_env v L (.inr rfl) (e₂.of_regs r₂) (fun _ _ => rfl) y22₂ o₂.rounds x26₂ x27₂ hn)
    fun g₁ g₂ ⟨ge₁, _, gf₁⟩ ⟨ge₂, _, gf₂⟩ => ?_
  have G₁ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) t₁.mem g₁.mem :=
    F₁.trans (by rw [r₁.mem] at gf₁; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₁)
  have G₂ : Frame (VG.Proof.AesGcm.AArch64.omFrame W) t₂.mem g₂.mem :=
    F₂.trans (by rw [r₂.mem] at gf₂; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₂)
  refine rel_seq (rel_taint [.x19] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac [ge₁.x19, ge₂.x19]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.ldr28_ok (V := BitVec.ofNat 64 tl) ge₁ (by rw [VG.Proof.AesGcm.AArch64.slot_kept G₁ sl (by decide) (by decide), o₁.sT]))
    (VG.Proof.AesGcm.AArch64.ldr28_ok (V := BitVec.ofNat 64 tl) ge₂ (by rw [VG.Proof.AesGcm.AArch64.slot_kept G₂ sl (by decide) (by decide), o₂.sT]))
    fun h₁ h₂ ⟨x28₁, q₁⟩ ⟨x28₂, q₂⟩ => ?_
  exact rel_taint [.x19, .x28] (by rw [q₁.sp, q₂.sp, ge₁.sp, ge₂.sp])
    (by agree_tac [x28₁, x28₂, q₁.others .x19 (by decide), q₂.others .x19 (by decide), ge₁.x19, ge₂.x19])
    ⟨_, by taint_decide⟩

/-- The rest of `openMain`, in two runs that agree on the tag. -/
theorem omB_rel (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s' m₁ m₂ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (VG.Proof.AesGcm.AArch64.workR W))
    (mo₁ : VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s m₁) (mo₂ : VG.Proof.AesGcm.AArch64.MidO Ctx W SP D Np A R nl al n tl s' m₂)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (VG.Proof.AesGcm.AArch64.omB v.callees) TT := by
  unfold VG.Proof.AesGcm.AArch64.omB
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq ?_ (VG.Proof.AesGcm.AArch64.omIte_ok v L hR ddW dcW mo₁) (VG.Proof.AesGcm.AArch64.omIte_ok v L hR ddW dcW mo₂)
    fun a b ⟨ea, xa, _, _⟩ ⟨eb, xb, _, _⟩ =>
      rel_taint [.x27] (by rw [ea.sp, eb.sp]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac [mo₁.env.x19, mo₂.env.x19])
      ⟨_, by taint_decide⟩) (VG.Proof.AesGcm.AArch64.ocLdr_ok mo₁.env mo₁.sD mo₁.sN) (VG.Proof.AesGcm.AArch64.ocLdr_ok mo₂.env mo₂.sD mo₂.sN)
      fun c₁ c₂ h₁ h₂ => ?_
    exact VG.Proof.AesGcm.AArch64.crypt_rel L v (VG.Proof.AesGcm.AArch64.oc_in hR mo₁ h₁) (VG.Proof.AesGcm.AArch64.oc_in hR mo₂ h₂)

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨hq, hres⟩ := hq
  have hR₁ : rounds (σ₁.gpr .x1) := (VG.Proof.AesGcm.AArch64.openLay h₁).1.rounds
  have hR₂ : rounds (σ₂.gpr .x1) := (VG.Proof.AesGcm.AArch64.openLay h₂).1.rounds
  obtain ⟨f₁, f₂⟩ := VG.Proof.AesGcm.AArch64.oneFacts (by decide : 2 < 3) (VG.Proof.AesGcm.AArch64.openCore h₁) (VG.Proof.AesGcm.AArch64.openCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
  have qg : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 16) 64 = stackArg σ₁ 2 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 16) 64 = stackArg σ₁ 2 := f₂.hW
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := qt.symm
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x12 0]) h).isSome = true := ⟨_, by taint_decide⟩
  refine rel_seq (RelCT.block_split (rel_seq (VG.Proof.AesGcm.AArch64.entryStash_rel (k := 16) (j := 8) (.inr rfl) rfl (.inr rfl) f₁ f₂
      (by decide) qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
      (VG.Proof.AesGcm.AArch64.entryStash_ok (V := stackArg σ₁ 1) (by decide) (by decide) hW₁ (f₁.hsp 2 (by decide)) (f₁.hsp 1 (by decide))
        hT₁ (f₁.argW (by decide)) rfl f₁.perm)
      (VG.Proof.AesGcm.AArch64.entryStash_ok (V := stackArg σ₁ 1) (by decide) (by decide) hW₂ (f₂.hsp 2 (by decide)) (f₂.hsp 1 (by decide))
        hT₂ (f₂.argW (by decide)) q0.symm f₂.perm)
      fun τ₁ τ₂ a₁ a₂ => rel_taint [] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac []) t₁))
    (VG.Proof.AesGcm.AArch64.openEntry_ok h₁) (VG.Proof.AesGcm.AArch64.openEntry_ok h₂) fun s₁ s₂ ⟨o₁, x12₁⟩ ⟨o₂, x12₂⟩ => ?_
  rw [f₂.hW, ← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qt, ← qg] at o₂
  rw [← qg] at x12₂
  have hb : (openRes σ₁).isSome = (openRes σ₂).isSome := by
    rw [openLeakOf, openLeakOf, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₁)),
      ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₂))] at hres
    revert hres; cases (openRes σ₁).isSome <;> cases (openRes σ₂).isSome <;> simp
  have hr₂ : openRes σ₂ = Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat)
      (ctxH σ₂.mem (σ₁.gpr .x0)) (stackArg σ₁ 1).toNat
      (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₂.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat) := by
    unfold openRes; rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qt, ← qg]
  rw [hr₂] at hb
  refine rel_seq (rel_taint [.x28] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.x28, o₂.x28])
      ⟨_, by taint_decide⟩)
    (tagLenOk_ok s₁ o₁.x28 o₁.tlt) (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun u₁ u₂ ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  have tr : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := o₁.of_regs r₁
  have p₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = stackArg σ₁ 0 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = stackArg σ₁ 0 := by rw [r₂.others _ (by decide), x12₂]
  have hlt : ((if Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat then 1 else 0 : Nat)) < 2 ^ 64 := by split <;> decide
  refine rel_seq (rel_ite (eval_zero x9₁ hlt) (eval_zero x9₂ hlt) (fun _ => ?_) (fun hf => ?_))
    (VG.Proof.AesGcm.AArch64.oite_ok v p₁ y12₁ x9₁) (VG.Proof.AesGcm.AArch64.oite_ok v p₂ y12₂ x9₂) fun w₁ w₂ e₁ e₂ =>
      rel_taint [.x19] (by rw [e₁.1.sp, e₂.1.sp]) (by agree_tac [e₁.1.x19, e₂.1.x19]) tr
  · exact rel_taint [] (by rw [p₁.env.sp, p₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  have hok : Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat = true := by
    revert hf; cases Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat <;> simp
  have hle := VG.Proof.AesGcm.AArch64.tagLenOk_le hok
  have L := p₁.lay
  refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [p₁.env.sp, p₂.env.sp])
      (by agree_tac [p₁.env.x19, p₂.env.x19, p₁.x28, p₂.x28, y12₁, y12₂]) ⟨_, by taint_decide⟩)
    (tagIn_ok p₁.env.x19 y12₁ p₁.x28 hle p₁.tagR p₁.env.perm.w (p₁.dtW.sub_right (Region.sub_prefix (by decide))))
    (tagIn_ok p₂.env.x19 y12₂ p₂.x28 hle p₂.tagR p₂.env.perm.w (p₂.dtW.sub_right (Region.sub_prefix (by decide))))
    fun t₁ t₂ ⟨rt₁, g₁, og₁, sp₁, rd₁, wr₁⟩ ⟨rt₂, g₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have p₁' := p₁.tagIn g₁ og₁ sp₁ rd₁ wr₁
  have p₂' := p₂.tagIn g₂ og₂ sp₂ rd₂ wr₂
  have rt₁' : bytesAt t₁.mem (stackArg σ₁ 2) (stackArg σ₁ 1).toNat =
      bytesAt σ₁.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat := by rw [rt₁, p₁.tag]
  have rt₂' : bytesAt t₂.mem (stackArg σ₁ 2) (stackArg σ₁ 1).toNat =
      bytesAt σ₂.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat := by rw [rt₂, p₂.tag]
  refine (VG.Proof.AesGcm.AArch64.openMain_split v.callees).symm.rel (rel_seq (VG.Proof.AesGcm.AArch64.omA_rel v p₁' p₂')
    (VG.Proof.AesGcm.AArch64.openMainA_ok v L p₁'.env p₁'.x22 p₁'.rounds p₁'.x23 p₁'.x24 p₁'.x26 p₁'.x27 p₁'.non p₁'.aad p₁'.dat p₁'.ddW
      p₁'.dcW p₁'.sA p₁'.sL p₁'.sD p₁'.sN p₁'.sT hok)
    (VG.Proof.AesGcm.AArch64.openMainA_ok v L p₂'.env p₂'.x22 p₂'.rounds p₂'.x23 p₂'.x24 p₂'.x26 p₂'.x27 p₂'.non p₂'.aad p₂'.dat p₂'.ddW
      p₂'.dcW p₂'.sA p₂'.sL p₂'.sD p₂'.sN p₂'.sT hok) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine VG.Proof.AesGcm.AArch64.omB_rel v L p₁'.rounds p₁'.ddW p₁'.dcW mo₁ mo₂ ?_
  rw [mo₁.x27, mo₂.x27, VG.Proof.AesGcm.AArch64.tagBit p₁' rt₁' hok, VG.Proof.AesGcm.AArch64.tagBit p₂' rt₂' hok]
  simp only [openRes] at hb
  rw [hb]

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamAadCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `absorb` by `absorb_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamAad_ct (v : GcmImpl) :
    ConstantTime isa streamAadAArch64.pre streamAadAArch64.pub (streamAad v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, qsp⟩ := hq
  simp only [streamAadAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q3, ← q4, ← q5] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x1 = St at *
  generalize hD : σ₁.gpr .x3 = D at *
  generalize hn : (σ₁.gpr .x4).toNat = n at *
  generalize hW : σ₁.gpr .x5 = W at *
  generalize ho : (σ₁.gpr .x2).toNat % 16 = o at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x4).isLt
  have ho₂ : (σ₂.gpr .x2).toNat % 16 = o := by rw [← q2, ho]
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hz : (Spec.Gcm.zeros o).length % 16 = o := by
    rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt (ho ▸ Nat.mod_lt _ (by decide))
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hσ : (σ.gpr .x2).toNat % 16 = o)
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = D ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x2).toNat % 16) ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      AbsIn Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros o) D n o σ' := by
    obtain ⟨he, hk, x23, x24, x25, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, by rw [x25, hσ], hz, ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [rd, wr, hrd]; simp), hlt, wd, dds, ddw⟩,
      rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, ← q1, q2, ← q3, q4, ← q5]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.aadEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (VG.Proof.AesGcm.AArch64.aadEntry_ok q0.symm q1.symm q3.symm (by rw [← q4, hn]) q5.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ ho a₁
  have j₂ := mk σ₂ τ₂ hrd₂ ho₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.absorb_rel L v (.inr rfl) j₁ j₂) (absorb_ok L (.inr rfl) v j₁) (absorb_ok L (.inr rfl) v j₂)
    fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.StreamInitCT`. -/
section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_init` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `j0` by `j0_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamInit_ct (v : GcmImpl) :
    ConstantTime isa streamInitAArch64.pre streamInitAArch64.pub (streamInit v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, qsp⟩ := hq
  simp only [streamInitAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q3, ← q4] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hNp : σ₁.gpr .x1 = Np at *
  generalize hn : (σ₁.gpr .x2).toNat = n at *
  generalize hSt : σ₁.gpr .x3 = St at *
  generalize hW : σ₁.gpr .x4 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x2).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩])
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = Np ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x26 = BitVec.ofNat 64 n ∧ σ'.gpr .x27 = 0 ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧ σ'.rd = σ.rd ∧
        σ'.wr = σ.wr) :
      J0In Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) Np n σ' := by
    obtain ⟨he, hk, x23, x24, x26, x27, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, x26, x27, ⟨VG.Proof.AesGcm.AArch64.covers_mem (by rw [rd, wr, hrd]; simp), hlt, wn, dns, dnw⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4] qsp
      (by agree_tac [hCtx, hNp, hSt, hW, ← q0, ← q1, q2, ← q3, ← q4]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesGcm.AArch64.siEntry_ok hCtx hNp hn hSt hW (perm σ₁ hrd₁ hwr₁))
    (VG.Proof.AesGcm.AArch64.siEntry_ok q0.symm q1.symm (by rw [← q2, hn]) q3.symm q4.symm
      (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ a₁
  have j₂ := mk σ₂ τ₂ hrd₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (VG.Proof.AesGcm.AArch64.j0_rel L v j₁ j₂) (j0_ok L v j₁) (j0_ok L v j₂) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.AArch64.Verified`. -/
section

/-!
# AES-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with no stack: the calls keep the return
address in `x30`, which each function saves in the working space).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String := (v.ctr.features ++ v.gh.features).dedup

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-! ## v8–v15 -/

theorem init_keepsV (v : GcmImpl) : (init v.callees).allInstrs keepsV = true := by
  simp only [init, ctrCall, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamInit_keepsV (v : GcmImpl) : (streamInit v.callees).allInstrs keepsV = true := by
  simp only [streamInit, j0, j0hash, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamAad_keepsV (v : GcmImpl) : (streamAad v.callees).allInstrs keepsV = true := by
  simp only [streamAad, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, VG.Impl.AesGcm.AArch64.tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1,
    absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tlTest, VG.Impl.AesGcm.AArch64.tagIn, cmpSeg, finBody, VG.Impl.AesGcm.AArch64.tag, crypt, crSeg1, crSeg2, crTail, ctrCall,
    ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», j0, j0hash, oneAad, encBody, fo, textAbs, finBody, VG.Impl.AesGcm.AArch64.tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openMain, oneCrypt, tagLenOk, tlTest, VG.Impl.AesGcm.AArch64.tagIn, cmpSeg, j0, j0hash, oneAad, decAbs, fo, textAbs,
    finBody, VG.Impl.AesGcm.AArch64.tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem init_correct (v : GcmImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (VG.Proof.AesGcm.AArch64.init_keepsV v)

theorem streamInit_correct (v : GcmImpl) (s : State) (hs : streamInitAArch64.pre s) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ streamInitAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamInit_wp v hs) (VG.Proof.AesGcm.AArch64.streamInit_keepsV v)

theorem streamAad_correct (v : GcmImpl) (s : State) (hs : streamAadAArch64.pre s) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ streamAadAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamAad_wp v hs) (VG.Proof.AesGcm.AArch64.streamAad_keepsV v)

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamEncrypt_wp v hs) (VG.Proof.AesGcm.AArch64.streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamDecrypt_wp v hs) (VG.Proof.AesGcm.AArch64.streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamFinish_wp v hs) (VG.Proof.AesGcm.AArch64.streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.streamVerify_wp v hs) (VG.Proof.AesGcm.AArch64.streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.seal_wp v hs) (VG.Proof.AesGcm.AArch64.seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcm.AArch64.open_wp v hs) (VG.Proof.AesGcm.AArch64.open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x2000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x2000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x5000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x5000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-- `tag` at 0 and `work` at `0x5000` (`[sp + 8]`). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8009 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 16⟩, ⟨0x5000, 2560⟩]

/-- `tag` at 0, `tag_len` 0 and `work` at `0x5000` (`[sp + 16]`). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified (v : GcmImpl) :
    Verified AArch64.target (init v.callees) (Proof.AesGcm.initScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.init_correct v) (VG.Proof.AesGcm.AArch64.init_ct v) (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, initAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [initSat] using VG.Proof.AesGcm.AArch64.initSat)

theorem streamInit_verified (v : GcmImpl) :
    Verified AArch64.target (streamInit v.callees) (Proof.AesGcm.streamInitScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamInit_correct v) (VG.Proof.AesGcm.AArch64.streamInit_ct v) (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, streamInitAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamInitSat] using VG.Proof.AesGcm.AArch64.streamInitSat)

theorem streamAad_verified (v : GcmImpl) :
    Verified AArch64.target (streamAad v.callees) (Proof.AesGcm.streamAadScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamAad_correct v) (VG.Proof.AesGcm.AArch64.streamAad_ct v) (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, streamAadAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamAadSat] using VG.Proof.AesGcm.AArch64.streamAadSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Proof.AesGcm.streamEncryptScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamEncrypt_correct v) (VG.Proof.AesGcm.AArch64.streamEncrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamEncryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using VG.Proof.AesGcm.AArch64.streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Proof.AesGcm.streamDecryptScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamDecrypt_correct v) (VG.Proof.AesGcm.AArch64.streamDecrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamDecryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using VG.Proof.AesGcm.AArch64.streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Proof.AesGcm.streamFinishScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamFinish_correct v) (VG.Proof.AesGcm.AArch64.streamFinish_ct v) (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, streamFinishAArch64, finPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [finSat] using VG.Proof.AesGcm.AArch64.finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Proof.AesGcm.streamVerifyScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.streamVerify_correct v) (VG.Proof.AesGcm.AArch64.streamVerify_ct v) (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost, streamVerifyAArch64, verPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [verSat] using VG.Proof.AesGcm.AArch64.verSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Proof.AesGcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.seal_correct v) (VG.Proof.AesGcm.AArch64.seal_ct v) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealAArch64, sealPre, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.AArch64.sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Proof.AesGcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesGcm.AArch64.open_correct v) (VG.Proof.AesGcm.AArch64.open_ct v) (by
    sig_implies [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
      Spec.Gcm.openPost, Spec.Gcm.openLeak, openAArch64, openPre, onePub, openRes, openLeakOf, args, rounds,
      AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.AArch64.openSat)

end VG.Proof.AesGcm.AArch64

end
