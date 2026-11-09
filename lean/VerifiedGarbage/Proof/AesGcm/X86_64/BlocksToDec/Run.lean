module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Contract
public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksToDec
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Tail
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Stitch
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Copy
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
public import VerifiedGarbage.Proof.AesGcm.X86_64.AlignedScratch
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: correctness

Untrusted: everything here is checked by Lean. As `BlocksTo` proves of
`vg_aes_gcm_encrypt_blocks_to`, whose code this is, with `Y` continued over
the ciphertext, read from `src` (`pt`), which nothing writes: `MidD s q k`
is `BlocksTo.Mid` with that `Y`, which holds after the entry, after the
out-of-place decryption loop (`mid_of_postToDec`, from `DPostTo`) and after
`rest`; the blocks left are copied to the output, decrypted there by a call
of `vg_aes_gcm_decrypt_blocks`, which hashes them as it reads them
(`blkD_call`), and their GHASH continues that of the first
(`ghashFrom_append`, `blocksAt_add`): `decrypt_wp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksToDec

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Proof.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Impl.AesGcm.X86_64.BlocksToDec (ghArgsTo ctrArgsTo tailTo decryptTo)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo DPostTo StitchToDecOkM)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 aesWith)

/-- The ciphertext of the first `q` blocks, at `src`. -/
abbrev pt (s : State) (q : Nat) : List Block := blocksAt s.mem (Src s) q

/-- The first `q` blocks decrypted into the output and their ciphertext
hashed, the arguments kept for what is left after `k` blocks. -/
structure MidD (s : State) (q k : Nat) (st : State) : Prop where
  q_le : q ≤ n s
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s k st.mem
  frame : Frame (wR s) s.mem st.mem
  data : blocksAt st.mem (Dst s) q = ct s q
  ctr : blockAt st.mem (C s) = Nat.repeat inc32 q (cb s)
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s q)

/-- What the function returns with. -/
def DoneD (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.blocksToDecPost s s'

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BT M s)
include hp

theorem mid_entry {s₁ : State} (hsp : s₁.gpr .rsp = s.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    MidD s 0 0 s₁ :=
  ⟨Nat.zero_le _, hsp, hcs, hrd, hwr, hk, frame_kR' hf, rfl,
    block_kR' hf (kR'_disj hp _ (by simp)).symm, block_kR' hf (kR'_disj hp _ (by simp)).symm⟩

/-- `MidD` through a frame of `scratch`'s slots that keeps the stack pointer
and the callee-saved registers. -/
theorem MidD.slots {q k k' : Nat} {st st' : State} (h : MidD s q k st)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hk : Kept s k' st'.mem)
    (hf : Frame [kR' s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : MidD s q k' st' := by
  refine ⟨h.q_le, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans (frame_kR' hf), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]
      exact (kR'_disj hp (dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega_arith)))
      (by have := hp.w_d; have := h.q_le; omega_arith)
  · rw [← h.ctr]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm
  · rw [← h.y]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = n s - n s % 16) {st : State} (h : MidD s q 0 st) :
    WP isa (.block rest) st (MidD s q q) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₇ : InRegions st.wr (S s + BitVec.ofNat 64 48) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kr := h.kept.src
  have kn := h.kept.n
  have kd := h.kept.dst
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kr kn kd
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_arith) (by omega_arith)
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have s₇₅ := sep 48 32 (by decide) (by decide) (by decide)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((st.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [rest, argSrc, argN, argDst]
    xrun [a₂, hS, r₅, r₆, r₇, w₅, w₆, w₇, kn, e15, esub, times16_val, kr, kd, s₅₇, s₅₆, s₆₇, s₇₅,
      Mem.readW_writeW_sep, Mem.readW_writeW_self64], ?_⟩
  refine h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => ?_) ?_ ?_ rfl rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega_arith
    · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega_arith)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

/-- `MidD` after the out-of-place loops, from what they leave. -/
theorem mid_of_postToDec {q k : Nat} {s₃ s₄ : State} (hqn : q ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 q)
    (hg : ∀ r ∈ BlocksTo.argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (h10 : s₃.gpr .r10 = Dst s) (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)))
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = s.wr) (hkp : Kept s k s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (P : DPostTo s₃ s₄) : MidD s q k s₄ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have data := P.data
  have ctr := P.ctr
  have frame := P.frame
  have y := P.y
  have hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have ek : s₃.gpr .rdi = K s := hg _ (by simp [BlocksTo.argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [BlocksTo.argRegs])
  have ec : s₃.gpr .rdx = C s := hg _ (by simp [BlocksTo.argRegs])
  have ey : s₃.gpr .rcx = Y s := hg _ (by simp [BlocksTo.argRegs])
  have ed : s₃.gpr .r8 = Src s := hg _ (by simp [BlocksTo.argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, h10, h11, hq9] at frame
  simp only [Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.cb,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr,
    Gcm.X86_64.Stitch.kp, ek, er, ec, ed, h10, hq9] at data
  simp only [Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.nb, ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, ey, ek, ed, hq9] at y
  have kd : ∀ r ∈ [kR' s], (kR M s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have eK : Spec.Aes.bytesAt s₃.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
      (by have := hp.w_k; have := M.ge; omega)
  have eH : blockAt s₃.mem (K s + 240) = hk s :=
    block_kR' hf₃ ((hp.k_s.sub_right kR'_sub).sub_left (Offset.sub_base (d := 240) _ (by have := M.ge; omega)))
  have eC : blockAt s₃.mem (C s) = cb s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  have eY : blockAt s₃.mem (Y s) = y₀ s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  have pr : Region.Sub ⟨Src s, 16 * q⟩ (srcR s) := Region.sub_prefix (by omega)
  have eS : blocksAt s₃.mem (Src s) q = blocksAt s.mem (Src s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.r_s.sub_left pr).sub_right kR'_sub)
    (by have := hp.w_r; omega)
  rw [eK, eC, eS] at data
  rw [eC] at ctr
  rw [eH, eY, eS] at y
  have pd : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega)
  have sk : Region.Disjoint (kR' s) ⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ :=
    Offset.base_disjoint _ (by have := AlignedScratch.offset_bounds aligned (S s); omega) (by have := hp.w_s; have := AlignedScratch.offset_bounds aligned (S s); omega)
  have fk : ∀ r ∈ [cR s, yR s, (⟨Dst s, 16 * q⟩ : Region), (⟨S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)), 1024⟩ : Region)],
      (kR' s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kR'_disj hp _ (by simp)
    · exact kR'_disj hp _ (by simp)
    · exact (kR'_disj hp (dR s) (by simp)).sub_right pd
    · exact sk
  have fw : Frame (wR s) s.mem s₄.mem := by
    refine (frame_kR' hf₃).trans (frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨cR s, by simp, fun _ h => h⟩
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, pd⟩
    · exact ⟨sR s, by simp, Offset.sub_base _ (by have := AlignedScratch.offset_bounds aligned (S s); omega)⟩
  refine ⟨hqn, ?_, fun r hr => ?_, P.rd.trans hrd, P.wr.trans hwr, hkp.frame frame fk, fw, data, ctr, y⟩
  · rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg _ (by simp [BlocksTo.argRegs])
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2]; exact hcs r hr

/-- The interleaved part, from the state after the entry. -/
theorem stitch_ok {piece : Prog isa} (hpiece : StitchToDecOkM M piece)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned) s₁ (MidD s (n s - n s % 16) 0) := by
  refine WP.seq (WP.mono (BlocksTo.cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega
    rw [h0]
    refine WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega
    refine WP.seq (WP.mono (BlocksTo.split_ok hp (s := s) (s₁ := s₂) (by rw [g₂]; exact hg _ (by decide) (by decide))
      (by rw [g₂, h11])) fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    have h10₃ : s₃.gpr .r10 = Dst s := by rw [g₃ _ (by decide) (by decide) (by decide), g₂, h10]
    have keepR : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r a b c d => by
      rw [g₃ r a b d, g₂, hg r d c]
    have ga : ∀ r ∈ BlocksTo.argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [BlocksTo.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide) (by decide)
    have gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact keepR _ (by decide) (by decide) (by decide) (by decide)
    have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    have hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    have hf₃ : Frame [kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    have hm : Gcm.X86_64.Stitch.nb s₃ % 16 = 0 := by
      have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      simp only [Gcm.X86_64.Stitch.nb, h9, toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega)]; omega
    exact WP.mono (hpiece s₃ (BlocksTo.spreTo_of hp (by omega) (by omega) h9 ga h10₃ h11₃ rd₃' wr₃' hf₃) hm) fun s₄ hP =>
      mid_of_postToDec hp (by omega) h9 ga gc h10₃ h11₃ rd₃' wr₃' hk₃ hf₃ hP

/-- With nothing left, `MidD` is the end. -/
theorem done_of {q : Nat} {st : State} (h : MidD s q q st) (h0 : n s - q = 0) : DoneD s st := by
  have hq : q = n s := by have := h.q_le; omega_arith
  subst hq
  exact ⟨⟨h.saved, keep_r hp h.frame⟩, h.data, h.ctr, h.y⟩

/-- The head of `tail`: `rcx` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {st : State} (h : MidD s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
      st fun st' => MidD s q q st' ∧ st'.zf = some (decide (n s - q = 0)) ∧
        st'.gpr .r11 = S s ∧ st'.gpr .rcx = BitVec.ofNat 64 (n s - q) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hz := and_self_beq (show n s - q < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₂, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], by rfl⟩
  exact h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags])
    h.kept (Frame.refl _ _) rfl rfl

/-- The pointers of the copy. -/
theorem ptrs_ok {q : Nat} {st : State} (h : MidD s q q st) (h11 : st.gpr .r11 = S s) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]) st
      fun st' => st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argSrc, argDst]; xrun [h11, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, by rfl, by rfl,
    by rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What the copy leaves: the ciphertext left in the output, nothing else
written. -/
theorem copy_ok {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st fun st' =>
      blocksAt st'.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) ∧
      Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hq := h.q_le
  have h16 := n16_lt hp
  have hwr := hp.w_r
  have hwd := hp.w_d
  have ss : Region.Sub ⟨sq s q, 16 * (n s - q)⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  have ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  have pre : CopyPre st (sq s q) (dq s q) (n s - q) :=
    ⟨hsi, hdi, hcx, by omega_arith, by omega_arith,
      Blocks.covers_off' (covers_of_mem (r := srcR s) (by rw [h.rd, h.wr, hp.rd]; simp)) (by omega_arith) (by omega_arith),
      Blocks.covers_off' (covers_of_mem (r := dR s) (by rw [h.wr, hp.wr]; simp)) (by omega_arith) (by omega_arith),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono (copyBlocks_wp st pre) fun st' ⟨hm, hg, hrd, hwr'⟩ => ⟨?_, ?_, hg, hrd, hwr'⟩
  · have e := bytesAt_writeBytes_self st.mem (dq s q) (Spec.Aes.bytesAt st.mem (sq s q) (16 * (n s - q)))
      (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, hm, e,
      bytesAt_frame h.frame (fun r hr => (src_wR hp r hr).sub_left ss) (by omega_arith)]
  · rw [hm]; exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `MidD` through the copy, which writes only the output past the first `q`
blocks. -/
theorem MidD.copy {q : Nat} {st st' : State} (h : MidD s q q st)
    (hf : Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem) (hsp : st'.gpr .rsp = st.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    MidD s q q st' := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  have one : ∀ {r : Region}, r.Disjoint ⟨dq s q, 16 * (n s - q)⟩ →
      ∀ r' ∈ [(⟨dq s q, 16 * (n s - q)⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨hq, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd, hwr.trans h.wr,
    h.kept.frame hf (one ((kR'_disj hp (dR s) (by simp)).sub_right ds)), h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (one (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (n := 16 * (n s - q))
      (Nat.le_refl _) (by omega_arith))) (by omega_arith)
  · rw [← h.ctr]; exact blockAt_frame hf (one (hp.c_d.sub_right ds))
  · rw [← h.y]; exact blockAt_frame hf (one (hp.y_d.sub_right ds))

/-- The arguments of `vg_aes_gcm_decrypt_blocks` on the output left. -/
theorem args_ok {q : Nat} {st : State} (h : MidD s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)),
        .mov .rsi (.mem (at_ .r11 argRounds)), .mov .rdx (.mem (at_ .r11 argCtr)),
        .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)), .mov .r9 (.mem (at_ .r11 argN)),
        .mov .rax (.reg .r11)]) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = C s ∧ st'.gpr .rcx = Y s ∧
      st'.gpr .r8 = dq s q ∧ st'.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st'.gpr .rax = S s ∧
      st'.gpr .rsp = SP s ∧ (∀ r ∈ calleeSaved, st'.gpr r = s.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [argCtx, argRounds, argCtr, argY, argDst, argN]
    xrun [a₂, hS, r₁, r₂, r₃, r₄, r₆, r₇, kc0, h.kept.rounds, h.kept.ctr, h.kept.y, h.kept.dst, h.kept.n], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, h.rsp],
    fun r hr => ?_, by rfl, by rfl, by rfl⟩
  rw [← h.saved r hr]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-- What the call needs, after the push of `scratch`. -/
theorem blkCall_of {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    BlkCall M (pushed [.rax] st) (K s) (C s) (Y s) (dq s q) (S s) (R s) (n s - q) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  have hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  have psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have harg : (pushed [.rax] st).mem.readW ((pushed [.rax] st).gpr .rsp) 64 = S s := by
    have := hpj 0 (by decide); rw [← h_ax]; rw [pushed_rsp]; exact this
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  have tt := pushed_tR (s := s) hsp
  have hdq : (dq s q).toNat = (Dst s).toNat + 16 * q := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * q) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hR : BitVec.ofNat 64 (R s) = s.gpr .rsi := by simp [R]
  have hok : M.ok st.mem (K s) := M.frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]) hp.w_k hp.ok
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h_di, by rw [pushed_gpr _ _ (by decide), h_si, hR],
    by rw [pushed_gpr _ _ (by decide)]; exact h_dx, by rw [pushed_gpr _ _ (by decide)]; exact h_cx,
    by rw [pushed_gpr _ _ (by decide)]; exact h_8, by rw [pushed_gpr _ _ (by decide)]; exact h_9, harg, hp.rounds,
    hp.w_k, hp.w_c, hp.w_y, by rw [hdq]; omega_arith, hp.w_s, ?_,
    hp.k_c, hp.k_y, hp.k_d.sub_right ds, hp.k_s, hp.c_y, hp.c_d.sub_right ds, hp.c_s, hp.y_d.sub_right ds, hp.y_s,
    hp.d_s.sub_left ds, by rw [tt]; exact hp.b_k, by rw [tt]; exact hp.b_c, by rw [tt]; exact hp.b_y,
    by rw [tt]; exact hp.b_d.sub_right ds, by rw [tt]; exact hp.b_s, ?_, ?_, ?_⟩
  · rw [psp, show SP s - BitVec.ofNat 64 8 - 8 = SP s - BitVec.ofNat 64 16 by rw [← Offset.sub_add_eq]; rfl,
      toNat_sub_ofNat (by omega_arith)]
    omega_arith
  · simp only [pushed_rd, pushed_wr, h.rd, h.wr, hp.rd, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by rw [pushed_rsp, hsp]; simp))
      (covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · simp only [pushed_wr, h.wr, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega_arith) (by omega_arith)
  · exact M.frame hpf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.b_k.sub_left (below_sub (by decide) (by decide))).symm) hp.w_k hok

/-- What the call leaves, after the frame's pop. -/
theorem call_ok (B : BlkFn M) {q : Nat} {st : State} (h : MidD s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    WP isa (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s] st.mem st'.mem ∧
      blocksAt st'.mem (dq s q) (n s - q) = ctr32 (aesWith (R s) (Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1))))
        (blockAt st.mem (C s)) (blocksAt st.mem (dq s q) (n s - q)) ∧
      blockAt st'.mem (C s) = Nat.repeat inc32 (n s - q) (blockAt st.mem (C s)) ∧
      blockAt st'.mem (Y s) = ghashFrom (blockAt st.mem (K s + 240)) (blockAt st.mem (Y s))
        (blocksAt st.mem (dq s q) (n s - q)) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  have hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax] (by decide) hn8
  have hpf' : Frame [below (SP s) 8] st.mem (pushed [.rax] st).mem := by rw [hsp] at hpf; exact hpf
  have b8 : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (tR s).Disjoint r → ∀ r' ∈ [below (SP s) 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  have eK : Spec.Aes.bytesAt (pushed [.rax] st).mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hpf' (one (hp.b_k.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge)))) (by have := hp.w_k; have := M.ge; omega_arith)
  have eC : blockAt (pushed [.rax] st).mem (C s) = blockAt st.mem (C s) := blockAt_frame hpf' (one hp.b_c)
  have eY : blockAt (pushed [.rax] st).mem (Y s) = blockAt st.mem (Y s) := blockAt_frame hpf' (one hp.b_y)
  have eD : blocksAt (pushed [.rax] st).mem (dq s q) (n s - q) = blocksAt st.mem (dq s q) (n s - q) :=
    blocksAt_frame hpf' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega_arith)
  have eH : blockAt (pushed [.rax] st).mem (K s + 240) = blockAt st.mem (K s + 240) :=
    blockAt_frame hpf' (one (hp.b_k.sub_right (Offset.sub_base (d := 240) _ (by have := M.ge; omega_arith))))
  refine WP.frame (by simp) (by decide) (by decide) hn8
    (WP.mono (blkD_call B (blkCall_of hp h hlt h_di h_si h_dx h_cx h_8 h_9 h_ax)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  have psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    refine (hpf'.sub fun r hr => ⟨tR s, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩).trans
      (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨tR s, by simp, ?_⟩
      have e : SP s - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP s - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] st).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)
  · rw [popped_mem]; rw [eK, eC, eD] at o₁; exact o₁
  · rw [popped_mem]; rw [eC] at o₂; exact o₂
  · rw [popped_mem]; rw [eH, eY, eD] at o₃; exact o₃

/-- The blocks left, from `MidD s q q`: copied and decrypted in place. -/
theorem tail_ok (B : BlkFn M) {q : Nat} {st : State} (h : MidD s q q st) : WP isa (tail B.dec) st (DoneD s) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have hwr := hp.w_r
  have h16 := n16_lt hp
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, h11, hcx, hm₁⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  have hlt : q < n s := by simp at e; omega_arith
  refine WP.seq (WP.mono (ptrs_ok hp M₁ h11) fun st₂ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have M₂ : MidD s q q st₂ := M₁.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
    (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.seq (WP.mono (copy_ok hp M₂ hlt hsi hdi (by rw [g₂ _ (by decide) (by decide), hcx]))
    fun st₃ ⟨hb₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have M₃ : MidD s q q st₃ := M₂.copy hp f₃ (g₃ _ (by decide) (by decide))
    (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.seq (WP.mono (args_ok hp M₃) fun st₄ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ => ?_)
  have M₄ : MidD s q q st₄ := M₃.slots hp (by rw [sp₄, M₃.rsp]) (fun r hr => by rw [cs₄ r hr, M₃.saved r hr])
    (by rw [m₄]; exact M₃.kept) (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄
  refine WP.mono (call_ok hp B M₄ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇) fun st₅ ⟨cs₅, rd₅, wr₅, f₅, o₁, o₂, o₃⟩ => ?_
  -- The values the call read.
  have hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    keep_sch hp M₄.frame
  have hH : blockAt st₄.mem (K s + 240) = hk s := keep_h hp M₄.frame
  have hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) := by rw [m₄]; exact hb₃
  rw [hK, M₄.ctr, hD₄] at o₁
  rw [M₄.ctr] at o₂
  rw [hH, M₄.y, hD₄] at o₃
  -- What the call wrote is apart from the first `q` blocks and the return address.
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega_arith)
  have keep : ∀ {r : Region}, r.Disjoint (cR s) → r.Disjoint (yR s) → r.Disjoint ⟨dq s q, (n s - q) * 16⟩ →
      r.Disjoint (sR s) → r.Disjoint (tR s) → ∀ r' ∈ [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s],
        r.Disjoint r' := by
    intro r a b c d e r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  have pq : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega_arith)
  have hfirst : blocksAt st₅.mem (Dst s) q = ct s q := by
    rw [← M₄.data]
    exact blocksAt_frame f₅ (keep (hp.c_d.symm.sub_left pq) (hp.y_d.symm.sub_left pq)
      (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (Nat.le_refl _) (by omega_arith))
      (hp.d_s.sub_left pq) (hp.b_d.symm.sub_left pq)) (by omega_arith)
  have hall : ct s (n s) = ct s q ++ ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (sq s q) (n s - q)) := by
    rw [ct, ← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Proof.Gcm.ctr32_append, Blocks.length_blocksAt,
      Nat.add_sub_cancel' hq]
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) (keep hp.t_c hp.t_y (hp.t_d.sub_right ds) hp.t_s
      (Offset.base_disjoint_below (SP s) (by omega_arith))) (by decide), keep_r hp M₄.frame]
  · show blocksAt st₅.mem (Dst s) (n s) = ct s (n s)
    rw [← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]
    rw [hfirst]; exact (congrArg (ct s q ++ ·) o₁).trans hall.symm
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [o₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s (n s))
    rw [o₃, ← Proof.Gcm.ghashFrom_append, pt, pt, ← Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]

end

/-! ## Out of place, with no copy -/

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- The calls' working space, after the arguments kept. -/
abbrev W5 (s : State) : Addr := S s + BitVec.ofNat 64 64

omit hp in
theorem w5_sub {k : Nat} (hk : k ≤ 2048) : Region.Sub ⟨W5 s, k⟩ (sR s) := Offset.sub_base _ (by omega_arith)

omit hp in
/-- A call's return address is in the stack below the arguments. -/
theorem ret_sub : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)

omit hp in
theorem h_sub : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR M s) :=
  Offset.sub_base _ (by have := M.ge; omega_arith)

omit hp in
theorem k_sub : Region.Sub ⟨K s, 240⟩ (kR M s) :=
  Region.sub_prefix (by have := M.ge; omega_arith)

omit hp in
theorem src_eq : (⟨Src s, 16 * n s⟩ : Region) = srcR s := by rw [Nat.mul_comm]

omit hp in
theorem dst_eq : (⟨Dst s, 16 * n s⟩ : Region) = dR s := by rw [Nat.mul_comm]

/-- The arguments of `vg_ghash` on the `n` blocks at `src`. -/
theorem ghArgsTo_ok {st : State} (h : MidD s 0 0 st) :
    WP isa (.block ghArgsTo) st fun st' =>
      GhCall st' (K s + BitVec.ofNat 64 240) (Y s) (Src s) (W5 s) (n s) ∧ st'.gpr .rsp = SP s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have h16 := n16_lt hp
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have ks0 : st.mem.readW (S s + BitVec.ofNat 64 32) 64 = Src s := by simpa using h.kept.src
  have kn0 : st.mem.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s) := by simpa using h.kept.n
  have s16 : Region.Sub ⟨W5 s, 256⟩ (sR s) := w5_sub (by decide)
  have pH := h_sub (s := s) (M := M)
  have rs := ret_sub (s := s)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ghArgsTo, argCtx, argY, argSrc, argN]
    xrun [a₂, hS, r₁, r₄, r₅, r₆, kc0, h.kept.y, ks0, kn0], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags], by omega_arith,
    hp.k_y.sub_left pH, (hp.k_s.sub_left pH).sub_right s16, by rw [src_eq]; exact hp.y_r,
    hp.y_s.sub_right s16, by rw [src_eq]; exact hp.r_s.sub_right s16, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [gpr_setReg, gpr_arithFlags, h.rsp], fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact (hp.b_k.sub_left rs).sub_right pH
  · exact hp.b_y.sub_left rs
  · rw [src_eq]; exact hp.b_r.sub_left rs
  · exact (hp.b_s.sub_left rs).sub_right s16
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨kR M s, by simp, 240, rfl, by have := M.ge; omega_arith⟩
    · exact ⟨srcR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨yR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 256 ≤ 2112)⟩
  · simp only [wr_setReg, wr_arithFlags, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 256 ≤ 2112)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- The arguments of `vg_aes_ctr32_to` on the `n` blocks, from `src` to
`dst`, with the arguments kept in memory `m`. -/
theorem ctrArgsTo_ok {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hk : Kept s 0 st.mem) (ha : st.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s) :
    WP isa (.block ctrArgsTo) st fun st' =>
      CtrToCall st' (K s) (C s) (Src s) (Dst s) (W5 s) (R s) (n s) ∧ st'.gpr .rsp = SP s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have h16 := n16_lt hp
  have hwr' := hp.w_r
  have hwd := hp.w_d
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [hrd, hwr, hsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by rw [hsp, ha]
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using hk.ctx
  have r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [hrd, hwr]; exact s_in' hp (by decide)
  have ks0 : st.mem.readW (S s + BitVec.ofNat 64 32) 64 = Src s := by simpa using hk.src
  have kn0 : st.mem.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s) := by simpa using hk.n
  have kd0 : st.mem.readW (S s + BitVec.ofNat 64 48) 64 = Dst s := by simpa using hk.dst
  have s48 : Region.Sub ⟨W5 s, 2048⟩ (sR s) := w5_sub (by decide)
  have pK : Region.Sub ⟨K s, 240⟩ (kR M s) := k_sub
  have rs := ret_sub (s := s)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ctrArgsTo, argCtx, argRounds, argCtr, argSrc, argN, argDst]
    xrun [a₂, hS, r₁, r₂, r₃, r₅, r₆, r₇, kc0, hk.rounds, hk.ctr, ks0, kn0, kd0], ?_⟩
  refine ⟨⟨by simp [gpr_setReg], by simp [gpr_setReg, R], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], hp.rounds,
    by omega_arith, by omega_arith,
    hp.k_c.sub_left pK, by rw [dst_eq]; exact hp.k_d.sub_left pK, (hp.k_s.sub_left pK).sub_right s48,
    by rw [src_eq]; exact hp.c_r, by rw [dst_eq]; exact hp.c_d, hp.c_s.sub_right s48,
    by rw [src_eq, dst_eq]; exact hp.r_d, by rw [src_eq]; exact hp.r_s.sub_right s48,
    by rw [dst_eq]; exact hp.d_s.sub_right s48, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [gpr_setReg, gpr_arithFlags, hsp], fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, hsp]
  · exact (hp.b_k.sub_left rs).sub_right pK
  · exact hp.b_c.sub_left rs
  · rw [src_eq]; exact hp.b_r.sub_left rs
  · rw [dst_eq]; exact hp.b_d.sub_left rs
  · exact (hp.b_s.sub_left rs).sub_right s48
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨kR M s, by simp, 0, by simp, by show 0 + 240 ≤ M.len; have := M.ge; omega_arith⟩
    · exact ⟨srcR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨cR s, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 2048 ≤ 2112)⟩
  · simp only [wr_setReg, wr_arithFlags, hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨cR s, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s, by simp, 0, by simp, by simp [Nat.mul_comm]⟩
    · exact ⟨sR s, by simp, 64, rfl, by exact (by decide : 64 + 2048 ≤ 2112)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- After the hash of the `n` blocks at `src`: `Y` continued over them, and
what the decryption needs (the arguments kept, the stack argument `scratch`,
the counter and the key context through a frame of the regions written and
the stack below the arguments). -/
structure GD (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s 0 st.mem
  arg : st.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctr : blockAt st.mem (C s) = cb s
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) (pt s (n s))

/-- The blocks at `src` hashed: the arguments of `vg_ghash` and its call. -/
theorem ghStep_ok (g : GhashImpl) {st : State} (h : MidD s 0 0 st) :
    WP isa (.seq (.block ghArgsTo) (.call g.fn.name g.fn.code)) st (GD s) := by
  have h16 := n16_lt hp
  have hwd := hp.w_d
  have hwr := hp.w_r
  refine WP.seq (WP.mono (ghArgsTo_ok hp h) fun st₂ ⟨G, sp₂, cs₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (gh_call g G) fun st₃ P₃ => ?_
  have rs := ret_sub (s := s)
  have s16 : Region.Sub ⟨W5 s, 256⟩ (sR s) := w5_sub (by decide)
  have k56 : (kR' s).Disjoint ⟨W5 s, 2048⟩ :=
    Offset.disjoint_of_le (by simp only [kR', W5]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.w_s; omega_arith)
      (by simp only [W5]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.w_s; omega_arith)
  have F₃ : Frame (wR s ++ [tR s]) s.mem st₃.mem := by
    refine (show Frame (wR s ++ [tR s]) s.mem st₂.mem by
      rw [m₂]; exact h.frame.mono fun r hr => List.mem_append_left _ hr).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨sR s, by simp, s16⟩
    · exact ⟨tR s, by simp, rs⟩
  have kept₃ : Kept s 0 st₃.mem := (m₂ ▸ h.kept).frame P₃.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.y_s.sub_right kR'_sub).symm
    · exact k56.sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_s.sub_left rs).symm.sub_left kR'_sub
  -- The stack argument `scratch`.
  have aS : Region.Disjoint (tR s) ⟨SP s + BitVec.ofNat 64 24, 8⟩ := by
    have := hp.w_t; have := hp.w_sp
    intro a h₁ h₂
    simp only [Region.Contains, tR, below, SP] at h₁ h₂
    bv_omega
  have hsA : Region.Sub ⟨SP s + BitVec.ofNat 64 24, 8⟩ (aR s) := by
    rw [show SP s + BitVec.ofNat 64 24 = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 16 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.sub_base _ (by omega_arith)
  have ha₃ : st₃.mem.readW (SP s + BitVec.ofNat 64 24) 64 = S s := by
    rw [F₃.readW (r := ⟨SP s + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.c_a.symm.sub_left hsA
      · exact hp.y_a.symm.sub_left hsA
      · exact hp.d_a.symm.sub_left hsA
      · exact hp.s_a.symm.sub_left hsA
      · exact aS.symm) (by decide)]
    rfl
  have hC₃ : blockAt st₃.mem (C s) = cb s := by
    rw [blockAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₂] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.c_y
      · exact hp.c_s.sub_right s16
      · exact (hp.b_c.sub_left rs).symm), m₂, h.ctr]
    rfl
  have o₃ := P₃.out
  rw [m₂, keep_h hp h.frame, h.y, blocksAt_frame h.frame (fun r hr => by rw [src_eq]; exact src_wR hp r hr)
    (by omega_arith)] at o₃
  exact ⟨by rw [P₃.saved _ (by decide), sp₂], fun r hr => by rw [P₃.saved r hr, cs₂ r hr, h.saved r hr],
    by rw [P₃.rd, rd₂, h.rd], by rw [P₃.wr, wr₂, h.wr], kept₃, ha₃, F₃, hC₃, by rw [o₃]; rfl⟩

/-- The blocks decrypted from `src` to `dst`: the arguments of
`vg_aes_ctr32_to` and its call. -/
theorem ctrStep_ok (v : Proof.Aes.X86_64.Ctr32ToImpl) {st : State} (G : GD s st) :
    WP isa (.seq (.block ctrArgsTo) (.call v.callee.name v.callee.code)) st (DoneD s) := by
  have h16 := n16_lt hp
  have hwd := hp.w_d
  have hwr := hp.w_r
  have rs := ret_sub (s := s)
  have s48 : Region.Sub ⟨W5 s, 2048⟩ (sR s) := w5_sub (by decide)
  refine WP.seq (WP.mono (ctrArgsTo_ok hp G.rsp G.rd G.wr G.kept G.arg) fun st₄ ⟨T, sp₄, cs₄, m₄, _, _⟩ => ?_)
  refine WP.mono (ctrTo_call v T) fun st₅ P₅ => ?_
  have F₅ : Frame (wR s ++ [tR s]) s.mem st₅.mem := G.frame.trans (by
    rw [← m₄]
    exact P₅.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₄] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨cR s, by simp, fun _ h => h⟩
      · exact ⟨dR s, by simp, by rw [dst_eq]; exact fun _ h => h⟩
      · exact ⟨sR s, by simp, s48⟩
      · exact ⟨tR s, by simp, rs⟩)
  -- What the call reads.
  have hRb : 16 * (R s + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have hK₄ : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    have hs : Region.Sub ⟨K s, 16 * (R s + 1)⟩ (kR M s) := Region.sub_prefix (by have := M.ge; omega_arith)
    rw [m₄]
    exact bytesAt_frame G.frame (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.k_c.sub_left hs
      · exact hp.k_y.sub_left hs
      · exact hp.k_d.sub_left hs
      · exact hp.k_s.sub_left hs
      · exact hp.b_k.symm.sub_left hs) (by omega_arith)
  have hS : blocksAt st.mem (Src s) (n s) = blocksAt s.mem (Src s) (n s) :=
    blocksAt_frame G.frame (fun r hr => by
      rw [src_eq]
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact src_wR hp r hr
      · exact hp.b_r.symm) (by omega_arith)
  have o₁ := P₅.out
  rw [hK₄, m₄, G.ctr, hS] at o₁
  have o₂ := P₅.ctr
  rw [m₄, G.ctr] at o₂
  have hY₅ : blockAt st₅.mem (Y s) = blockAt st.mem (Y s) := by
    rw [← m₄]
    exact blockAt_frame P₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sp₄] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.c_y.symm
      · rw [dst_eq]; exact hp.y_d
      · exact hp.y_s.sub_right s48
      · exact (hp.b_y.sub_left rs).symm)
  refine ⟨⟨fun r hr => by rw [P₅.saved r hr, cs₄ r hr, G.saved r hr], ?_⟩, o₁, o₂, by rw [hY₅, G.y]⟩
  show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
  exact F₅.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.t_c
    · exact hp.t_y
    · exact hp.t_d
    · exact hp.t_s
    · exact Offset.base_disjoint_below (SP s) (by omega_arith)) (by decide)

/-- The blocks, from `MidD s 0 0`: hashed at `src`, then decrypted from
`src` to `dst`. -/
theorem tailTo_ok (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) {st : State} (h : MidD s 0 0 st) :
    WP isa (tailTo g.fn ⟨v.callee.name, v.callee.code⟩) st (DoneD s) := by
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, _, _, _⟩ => ?_)
  refine WP.ite (decide (n s - 0 = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun _ => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  exact WP.seq (WP.mono (ghStep_ok hp g M₁) fun _ G => ctrStep_ok hp v G)

end

theorem decrypt_wp {M : CtxMode} (B : BlkFn M) (aligned : Bool) (st : Option (Prog isa))
    (hst : ∀ p, st = some p → StitchToDecOkM M p) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (BlocksToDec.decrypt B.dec st aligned) s (DoneD s) := by
  have hp := BT.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => ?_)
  cases st with
  | none =>
    exact WP.seq (WP.block_nil (tail_ok hp B (mid_entry hp (hg _ (by decide) (by decide))
      (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      hk hf hrd hwr)))
  | some p =>
    exact WP.seq (WP.seq (WP.mono (stitch_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
      WP.mono (rest_ok hp rfl M) fun st' M' => tail_ok hp B M'))

/-- `decryptTo`: the entry, then the blocks hashed at `src` and decrypted
from `src` to `dst`, with no copy. -/
theorem decryptTo_wp {M : CtxMode} (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (decryptTo g.fn ⟨v.callee.name, v.callee.code⟩) s (DoneD s) := by
  have hp := BT.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨_, _, hg, hk, hf, hrd, hwr⟩ => ?_)
  exact tailTo_ok hp g v (mid_entry hp (hg _ (by decide) (by decide))
    (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
    hk hf hrd hwr)

end VG.Proof.AesGcm.X86_64.BlocksToDec
