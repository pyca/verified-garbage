module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody

/-! ### `AesGcm.X86_64.Split.Fin`, which this module and modules that import it used -/

section

/-!
# AES-GCM `seal_split` on x86-64: the end

Untrusted: everything here is checked by Lean. After `oneBlocks` and the
total length `N` put back where it keeps the length of what it encrypted,
`seal_split` ends as its instance's `seal` does: `FinOk` states what that
end must do, as `Short.finishF_ok` proves of `Short.finishWith` (the
instances ending without calls), and `finCalls_ok` of `oneCrypt` and
`oneTag 0` (`SealSplit.finCalls`, the others), as `sealBody_ok` uses them.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk finishF_ok)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- What the end `fin` of `seal_split` does after `oneBlocks` (from `s` to
`s₃`) and the total length `N` put back. -/
def FinOk (M : CtxMode) (fin : Prog isa) : Prop :=
  ∀ {Ctx W SP : Addr}, Lay Ctx (W + BitVec.ofNat 64 16) W SP →
    ∀ {R : Nat} {D : Addr} {n al N : Nat} {H icb : Block} {a : List Byte} {s s₃ : State},
    ObPre M Ctx W SP R D n s → Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ → s₃.rd = s.rd → s₃.wr = s.wr →
    Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₃.mem →
    s₃.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N → N < 2 ^ 64 →
    s₃.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)) →
    s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16) →
    OutE Ctx W R D (n / 16) s s₃ → blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H →
    blockAt s.mem (cbA W) = icb → s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al →
    Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)) →
    WP isa fin s₃ fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (oneFrameB W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))

/-- The end without calls, with the keystream of `ks`. -/
theorem finOk_finishWith {M : CtxMode} (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) :
    FinOk M (Short.finishWith ks) := by
  intro Ctx W SP L R D n al N H icb a s s₃ h he₃ rd₃ wr₃ fr₃ tl₃ _ dat₃ len₃ o hH hcb hal habs
  exact finishF_ok L hF hks h he₃ rd₃ wr₃ fr₃ tl₃ dat₃ len₃ o hH hcb hal habs

/-- The end with calls: `oneCrypt` and `oneTag 0`. -/
theorem finCalls_ok (v : GcmImpl) {M : CtxMode} : FinOk M (SealSplit.finCalls v.callees) := by
  intro Ctx W SP L R D n al N H icb a s s₃ h he₃ rd₃ wr₃ fr₃ tl₃ hN dat₃ len₃ o hH hcb hal habs
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hR := h.rounds.2
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨o₁, o₂, o₃⟩ := o
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h fr₃ hH hcb habs hxa o₁ o₂
    (Z := bytesAt s₃.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega_using [])
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  have hP : 16 * (n / 16) % 16 = 0 := by omega_using []
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (h.data.of_eq rd₃ wr₃).drop (by omega_using [])
  have hlen₃ : s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [len₃]; congr 1; omega_using []
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) (by decide), hal]
  unfold SealSplit.finCalls
  refine WP.seq (WP.mono (oneCrypt_ok v L (icb := icb) hP he₃ hR₃ dat₃ hlen₃ hdw) fun s₄ ⟨co, rd₄, wr₄⟩ => ?_)
  have out₄ := co.out ct₃
  have g₄ := crFrame_one co.frame
  have hDW' := hdw.ok.w
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => g₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW' hd)
      (by decide)
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdw r hr).sub_left (Lay.ctxSub (by decide))), hH₃]
  have abs₄ : Absorbed s₄.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))) := by
    have hl := Nat.mod_lt (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length
      (show 16 > 0 by decide)
    exact ab₃.congr (blockAt_frame co.frame (st_crFrame L hdw.ok (d := 16) (k := 16) (by decide)))
      (bytesAt_frame co.frame (st_crFrame L hdw.ok (d := 32) (by omega_using [])) (by omega_using []))
  have hX : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega_using [hxa]
  refine WP.mono (oneTag_ok v L (o := 0) (al := al) (.inl rfl) hX co.env hH₄ co.rounds
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact dat₃)
    (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₃)
    (by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact tl₃) hN
    (by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hal₃) (hdw.ok.of_eq rd₄ wr₄) hDW')
    fun s₅ ⟨he₅, f₅, rd₅, wr₅, _, _, hq⟩ => ?_
  have T := hq abs₄
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' (by omega_using [])]
  have dDw : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact h.data.ok.stk.symm
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ dDw (by omega_using [hlt])
  have hp₄ : bytesAt s₄.mem D (16 * (n / 16)) = bytesAt s₃.mem D (16 * (n / 16)) :=
    bytesAt_frame co.frame (pre_crFrame (h.data.ok.of_eq rd₃ wr₃) (by omega_using [])) (by omega_using [hlt])
  have hc₄ : ciphOf s₄.mem Ctx R = ciphOf s.mem Ctx R := by rw [ciph_frame co.frame (ctx_crFrame L hdw) hR, hc₃]
  have hJ₄ : blockAt s₄.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [← hJ₃]; simpa using blockAt_frame co.frame (st_crFrame L hdw.ok (d := 0) (k := 16) (by decide))
  have hC : bytesAt s₅.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) := by
    rw [hd₅, split, split s.mem, hp₄, out₄, hw₃, hc₃, ht₃, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add]
  have eX : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16)) ++
      bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s₅.mem D n := by
    rw [hd₅, split, hp₄, List.append_assoc]
  rw [eX, padded_eq, hc₄, hJ₄, show W + BitVec.ofNat 64 0 = W from BitVec.add_zero W] at T
  exact ⟨he₅, rd₅.trans (rd₄.trans rd₃), wr₅.trans (wr₄.trans wr₃),
    oneB_trans f₃ (oneB_trans (oneFrame_B (by omega_using []) g₄)
      (oneFrame_B (k := 16 * (n / 16)) (by omega_using []) (wFrame_one (o := 0) (.inl rfl) f₅))), hC, T⟩

end VG.Proof.AesGcm.X86_64.Split

end

end

/-!
# AES-GCM `seal_split` on x86-64: the whole blocks at `dst` and the end

Untrusted: everything here is checked by Lean. In the frame of one word,
`seal`'s whole blocks (`oneBlocks`), the total length put back (`fixTlen`)
and its end (any `fin` doing what `FinOk` says) encrypt the data
left, from the counter block and the accumulator `prefix` left, and write the
tag of everything absorbed with the lengths block of the total length
(`inner_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ghash blocks ofBytes toBytes zeros
  padLen)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- The total length put back. -/
theorem fixTlen_ok {Ctx W SP : Addr} {N : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    WP isa (.block SealSplit.fixTlen) s fun s' => s'.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 N) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain w₁ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  unfold SealSplit.fixTlen
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, w₁, haux], ?_, ?_, ?_, ?_⟩
  · simp [mem_setReg, he.r15, haux]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals simp [rd_setReg, wr_setReg]

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : CtxMode}
include L

/-- `oneBlocks`, the total length `N` put back, and the end, from the
counter block `icb` and an accumulator holding `a` padded. -/
theorem inner_ok (B : BlkFn M) {fin : Prog isa} (hfin : FinOk M fin) {R : Nat} {D : Addr} {n al N : Nat} {H icb : Block}
    {a : List Byte} {s : State} (h : ObPre M Ctx W SP R D n s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64) :
    WP isa (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (oneFrameB W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := h.data.ok.w
  refine WP.seq (WP.mono (oneBlocksE_ok L B h) fun s₃ ⟨P, o⟩ => ?_)
  obtain d216 : ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Offset.disjoint W (.inr (by decide)) (by have := L.ww; omega_arith) (by have := L.ww; omega_arith)
    · exact ob_slots L hD (by have := h.data.ok.lt; omega_arith) h.t_w (by decide) (by decide) r hr
  obtain a₃ : s₃.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N := by
    rw [P.frame.readW (Region.contains_self _ _) d216 (by decide), haux]
  refine WP.seq (WP.mono (fixTlen_ok P.env a₃) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
  obtain he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := P.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide)) rd₄ wr₄
  obtain fW : Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_refl _) (by decide) (by have := L.ww; omega_arith))
  obtain f₄ : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₄.mem :=
    P.frame.trans (fW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩)
  obtain one : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 24⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 192, 24⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain k₄ : ∀ d, d = 200 ∨ d = 208 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd
    rw [m₄]
    rcases hd with rfl | rfl <;>
      exact Mem.readW_writeW_sep (Offset.sep W (.inr (by decide)) (by have := L.ww; omega_arith) (by have := L.ww; omega_arith))
        (by decide)
  obtain ⟨o₁, o₂, o₃⟩ := o
  obtain eB : blocksAt s₄.mem D (n / 16) = blocksAt s₃.mem D (n / 16) :=
    blocksAt_frame fW (one ((hD.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))))
      (by have := h.data.ok.wrap; omega_arith)
  obtain eC : blockAt s₄.mem (cbA W) = blockAt s₃.mem (cbA W) :=
    blockAt_frame fW (one (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  obtain eY : blockAt s₄.mem (yA W) = blockAt s₃.mem (yA W) :=
    blockAt_frame fW (one (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  exact hfin L h he₄ (rd₄.trans P.rd) (wr₄.trans P.wr) f₄
    (by rw [m₄, Mem.readW_writeW_self64]) hN (by rw [k₄ 200 (.inl rfl)]; exact P.dat) (by rw [k₄ 208 (.inr rfl)]; exact P.len)
    ⟨by rw [eB, o₁], by rw [eC, o₂], by rw [eY, eB, o₃]⟩ hH hcb hal habs

end

/-- The stack below `SP - 8`, in the 56 bytes below `SP`. -/
theorem below8_sub {SP : Addr} {k : Nat} (hk : k + 8 ≤ 56) :
    Region.Sub (below (SP - BitVec.ofNat 64 8) k) (below SP 56) :=
  fun a h => below_sub (by omega_arith) (by decide) a (below_below SP 8 k a h)

/-- What a state may access, after a push. -/
theorem perm_pushed {Ctx St W : Addr} {s : State} (P : Perm Ctx St W s) : Perm Ctx St W (pushed [.rax] s) :=
  ⟨by rw [pushed_rd, pushed_wr]; exact covers_ins P.ctx, by rw [pushed_wr]; exact covers_tail P.st,
    by rw [pushed_wr]; exact covers_tail P.w⟩

/-- The push of one word: the word below `SP` written, and `rsp` a word lower. -/
theorem push_frame {Ctx St W SP : Addr} {s : State} (he : Env Ctx St W SP s) (sp : 8 ≤ SP.toNat) :
    Frame [below SP 8] s.mem (pushed [.rax] s).mem ∧ (pushed [.rax] s).gpr .rsp = SP - BitVec.ofNat 64 8 := by
  obtain hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [he.rsp]; simpa using sp
  obtain ⟨hf, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  exact ⟨by have := hf; rw [he.rsp] at this; exact this, by rw [pushed_rsp, he.rsp]; rfl⟩

/-- The environment, a word lower. -/
theorem env_pushed {Ctx St W SP : Addr} {s : State} (he : Env Ctx St W SP s) :
    Env Ctx St W (SP - BitVec.ofNat 64 8) (pushed [.rax] s) :=
  ⟨by rw [pushed_gpr _ _ (by decide)]; exact he.r13, by rw [pushed_gpr _ _ (by decide)]; exact he.r14,
    by rw [pushed_gpr _ _ (by decide)]; exact he.r15, by rw [pushed_rsp, he.rsp]; rfl, perm_pushed he.perm⟩

/-- The layout, a word lower. -/
theorem lay_pushed {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
    (kc : (below SP 56).Disjoint ⟨Ctx, 256⟩) (kw : (below SP 56).Disjoint ⟨W, 2560⟩) :
    Lay Ctx (W + BitVec.ofNat 64 16) W (SP - BitVec.ofNat 64 8) :=
  ⟨L.cw, L.sw, L.ww, L.cs, L.cw', L.sa, L.sb, kc.sub_left (below8_sub (by decide)),
    (kw.sub_right (Lay.wSub (by decide))).sub_left (below8_sub (by decide)), kw.sub_left (below8_sub (by decide)), L.big, L.nlt⟩

/-- What `seal_split` writes after `prefix`: `W` but its saved registers,
the data, and the 56 bytes below `SP`. -/
abbrev splitFrame (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 192, 32⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 56]

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : CtxMode}
include L

/-- `body`: `inner_ok` in the frame of one word, below `SP`. -/
theorem body_ok (B : BlkFn M) {fin : Prog isa} (hfin : FinOk M fin) {R : Nat} {D : Addr} {n al N : Nat} {H icb : Block}
    {a : List Byte} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (kw : (below SP 56).Disjoint ⟨W, 2560⟩) (kd : (below SP 56).Disjoint ⟨D, n⟩)
    (kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩) (sp : 56 ≤ SP.toNat)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64) :
    WP isa (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)) s
      fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  obtain hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [he.rsp]; simp; omega_arith
  obtain ⟨f₀, psp⟩ := push_frame he (by omega_arith)
  obtain b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  obtain one : ∀ {r : Region}, (below SP 56).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  obtain kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  obtain L' := lay_pushed L kc kw
  obtain rW : ∀ d, d + 8 ≤ 2560 →
      (pushed [.rax] s).mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₀.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (one (kw.sub_right (Lay.wSub hd))) (by decide)
  obtain bW : ∀ d, d + 16 ≤ 2560 → blockAt (pushed [.rax] s).mem (W + BitVec.ofNat 64 d) = blockAt s.mem (W + BitVec.ofNat 64 d) :=
    fun d hd => blockAt_frame f₀ (one (kw.sub_right (Lay.wSub hd)))
  obtain hu : ObPre M Ctx W (SP - BitVec.ofNat 64 8) R D n (pushed [.rax] s) :=
    ⟨env_pushed he,
     ⟨by rw [rW 176 (by decide)]; exact hR.1, hR.2⟩, by rw [rW 200 (by decide)]; exact hdat,
     by rw [rW 208 (by decide)]; exact hlen,
     ⟨⟨by rw [pushed_rd, pushed_wr]; exact covers_ins hd.ok.rd, hd.ok.lt, hd.ok.wrap, hd.ok.st, hd.ok.w,
        kd.sub_left (below8_sub (by decide))⟩, by rw [pushed_wr]; exact covers_tail hd.wr, hd.ctx⟩,
     kc.sub_left (below8_sub (by decide)), kw.sub_left (below8_sub (by decide)), kd.sub_left (below8_sub (by decide)),
     by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith,
     ⟨X.w, X.cs, X.cw, X.cd, kM.sub_left (below8_sub (by decide)), by rw [pushed_rd, pushed_wr]; exact covers_ins X.cov,
      M.frame f₀ (one kM) X.w X.ok⟩⟩
  obtain hH' : blockAt (pushed [.rax] s).mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f₀ (one (kc.sub_right (Offset.sub_base (d := 240) _ (by decide)))), hH]
  obtain bA : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W, 2560⟩ → blockAt (pushed [.rax] s).mem p = blockAt s.mem p :=
    fun hs => blockAt_frame f₀ (one (kw.sub_right hs))
  obtain hcb' : blockAt (pushed [.rax] s).mem (cbA W) = icb := by
    rw [bA (fun a hc => st_w a (cb_sub a hc))]; exact hcb
  obtain habs' : Absorbed (pushed [.rax] s).mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)) := by
    obtain hm := Nat.mod_lt (a ++ zeros (padLen a.length)).length (show 16 > 0 by decide)
    refine ⟨by rw [bA (fun a hc => st_w a (y_sub a hc))]; exact habs.1, ?_⟩
    rw [bytesAt_frame f₀ (one (kw.sub_right (fun a hc => st_w a
      (Offset.sub_base (W + BitVec.ofNat 64 16) (d := 32) (k := 80) (by omega_arith) a hc)))) (by omega_arith)]
    exact habs.2
  obtain hc : ciphOf (pushed [.rax] s).mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₀ (one kc) hR.2
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (inner_ok L' B hfin (al := al) (N := N) hu hH' hcb'
    (by rw [rW 184 (by decide)]; exact hal) habs' (by rw [rW 216 (by decide)]; exact haux) hN)
    fun s₂ ⟨e₂, rd₂, wr₂, f₂, hC, hT⟩ => ⟨by rw [e₂.rsp, psp], by rw [wr₂], ?_⟩)
  obtain prd : (popped .rax 1 s₂).rd = s.rd := by rw [popped_rd, rd₂, pushed_rd]
  obtain pwr : (popped .rax 1 s₂).wr = s.wr := by rw [popped_wr, wr₂, pushed_wr]; rfl
  refine ⟨⟨by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact e₂.r13,
    by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact e₂.r14,
    by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact e₂.r15,
    by rw [popped_rsp, e₂.rsp]; exact BitVec.sub_add_cancel _ _, he.perm.of_eq prd pwr⟩, prd, pwr, ?_, ?_, ?_⟩
  · rw [popped_mem]
    refine (f₀.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨below SP 56, by simp, b8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨below SP 56, by simp, below8_sub (by decide)⟩
  · rw [popped_mem, hC, hc, bytesAt_frame f₀ (one kd) (by have := hd.ok.wrap; omega_arith)]
  · rw [popped_mem, hT, hc, bW 16 (by decide)]

end

/-- What `seal_split` needs of its code after `prefix`, with the data left
at `D`: what `SealSplit.body` does (`body_ok`). -/
def BodyOk (M : CtxMode) (body : Prog isa) : Prop :=
  ∀ {Ctx W SP : Addr}, Lay Ctx (W + BitVec.ofNat 64 16) W SP →
    ∀ {R : Nat} {D : Addr} {n al N : Nat} {H icb : Block} {a : List Byte} {s : State},
    Env Ctx (W + BitVec.ofNat 64 16) W SP s → RoundsAt s.mem W R →
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D → s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n →
    DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n →
    (below SP 56).Disjoint ⟨W, 2560⟩ → (below SP 56).Disjoint ⟨D, n⟩ → (below SP 56).Disjoint ⟨Ctx, M.len⟩ →
    56 ≤ SP.toNat → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s →
    blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H → blockAt s.mem (cbA W) = icb →
    s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al →
    Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)) →
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N → N < 2 ^ 64 →
    WP isa body s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))

theorem bodyOk_body {M : CtxMode} (B : BlkFn M) {fin : Prog isa} (hfin : FinOk M fin) :
    BodyOk M (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)) :=
  fun L _ _ _ _ _ _ _ _ _ he hR hdat hlen hd kw kd kM sp X hH hcb hal habs haux hN =>
    body_ok L B hfin he hR hdat hlen hd kw kd kM sp X hH hcb hal habs haux hN

end VG.Proof.AesGcm.X86_64.Split
