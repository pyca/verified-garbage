module

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Seal

import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneShot

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. A tag length `tagLenOk` does
not allow gives 0. Any other: `J₀` and the additional data (AES-GCM's
`oneAad`), the tag of the ciphertext (`oneTag 112`), the received tag, read
from `tag`, padded (AES-GCM's `recv`) and compared (its `cmp 112`), and if
they match the data decrypted (`oneCrypt`); if not, the data stays as it was:
GCM-AD (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm tagLenOk recv cmp uO tlO auxO oneAad restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH gctr inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk SavedAt blockAt_frame bytesAt_frame exit_ok ret_kept
  covers_left padded_eq length_bytesAt recv_ok cmp_ok tagLenOk_ok bytesAt_take eval_e WP.run oneR and_self_beq)

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `OneEntry`, after code that writes only the tag length's slot. -/
theorem OneEntry.keep {s₀ s s' : State} {A D : Addr} {n : Nat} (E : OneEntry s₀ Ctx W SP A D n s)
    (hg : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneEntry s₀ Ctx W SP A D n s' := by
  have kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega_arith) h' (by decide)) (by decide)
  refine ⟨E.env.keep (fun r hr => ?_) hrd hwr, by rw [kp 232 (.inr (by decide)) (by decide)]; exact E.aad,
    by rw [kp 184 (.inl (by decide)) (by decide)]; exact E.alen, by rw [kp 200 (.inl (by decide)) (by decide)]; exact E.dat,
    by rw [kp 208 (.inl (by decide)) (by decide)]; exact E.len, by rw [kp 192 (.inl (by decide)) (by decide)]; exact E.tlen,
    by rw [hg _ (by simp)]; exact E.r12, by rw [hg _ (by simp)]; exact E.rbp, by rw [hg _ (by simp)]; exact E.rsp,
    E.saved.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)),
    E.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩), hrd.trans E.rd, hwr.trans E.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by simp)

end

/-- The entry of `open`, and the tag length kept at `W + 224`. -/
theorem openEntry_ok {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .rcx = A)
    (hD : s.gpr .r9 = D) (hn : (stackArg s 0).toNat = n) (hW : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = W) :
    WP isa (.block (oneEntry 32 ++ ([.mov .rbx (.mem (at_ .rsp 24)), .store (at_ .r15 tlO) .rbx] : List Instr))) s
      fun s₁ => OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 2 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 2 ∧ Frame [oneR W] s.mem s₁.mem := by
  have L := C.lay
  have a₄ := C.args 3 (by decide)
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW a₄) fun s₁ E => ?_)
  have a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [E.rd, E.wr]; exact C.args 2 (by decide)
  have ht : s₁.mem.readW (SP + BitVec.ofNat 64 24) 64 = stackArg s 2 := by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 24, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 4⟩ := by
        rw [show (24 : Nat) = 8 + 16 by rfl, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
        exact Offset.sub_base _ (by decide)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    rfl
  have w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 24)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 2 ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 2) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₃, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, ht]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, ht]
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₂, run₂, E.keep L (fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hrd₂ hwr₂ f₂, hbx₂,
    by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  exact E.frame.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- A region disjoint from what `open` writes before it compares the tags,
but for the data: `W` and the stack below `SP`. -/
def OutWS (W SP : Addr) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub (below SP stkN) → X.Disjoint r

/-- A region disjoint from `W`, the data and the stack below `SP`. -/
def OutWDS (W D SP : Addr) (n : Nat) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN) → X.Disjoint r

theorem OutWDS.ws {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) : OutWS W SP X :=
  fun r hr => h r (hr.elim .inl fun h => .inr (.inr h))

theorem OutWS.tagFrame {W SP : Addr} {X : Region} (h : OutWS W SP X) {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Lay.wSub ho))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr fun _ h => h)

theorem OutWDS.oneFrame {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) :
    ∀ r ∈ oneFrame W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Region.sub_prefix (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr fun _ h => h))

theorem ite_ofNat (p : Prop) [Decidable p] :
    (if p then 1 else 0 : BitVec 64) = BitVec.ofNat 64 (if p then 1 else 0) := by split <;> rfl

/-- After the comparison, from `s`: `k` is 1 if the tag of the ciphertext
matches the received one, and 0 if not, in ZF and at `W + 216`; the counter
block kept, and the first one (after `J₀ = J`) at the state's start. -/
structure OpenMid (Ctx W SP : Addr) (J : Block) (k : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  frame : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cb : blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
  zf : s'.zf = some (decide (k = 0))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  j : blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 J

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The tag of the ciphertext (`x`, absorbed, then the `n` bytes at `D`, of `N`
in all), compared with the received one. -/
theorem openCheck_ok {t : Nat} {D : Addr} {n N al : Nat} {H J : Block}
    {x : List Byte} (hx16 : x.length % 16 = 0) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hN₁ : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hCD : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (habs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x)
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J) {Tp : Addr}
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : OutWS W SP ⟨Tp, t⟩)
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 16, 8⟩) :
    WP isa (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv
      (.seq (cmp uO)
        (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))) s
      (OpenMid Ctx W SP J (if (toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
          zeros (padLen (x ++ bytesAt s.mem D n).length))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx J)).take t = bytesAt s.mem Tp t then 1 else 0) s) := by
  have La := L.lay
  have hlt := hd.lt
  -- The tag.
  refine WP.seq (WP.mono (oneTag_ok v L (o := 112) (al := al) (.inr rfl) hx16 he hH hdat hlen hN₁ hN hal hd hDW hCD)
    fun s₃ ⟨he₃, f₃, hrd₃, hwr₃, hcb₃, hj₃, hq⟩ => ?_)
  have hT₃ := hq habs
  rw [hj] at hT₃
  generalize hT : toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
    zeros (padLen (x ++ bytesAt s.mem D n).length)))) [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx J) = T
    at hT₃ ⊢
  have f₃' := wFrame_one (D := D) (n := n) (.inr rfl) f₃
  have kp₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => f₃'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd')
      (by decide)
  have hTp₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame f₃ (oT.tagFrame (o := 112) (by decide)) (by omega_arith)
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp := by
    rw [f₃.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (oA.tagFrame (o := 112) (by decide))
      (by decide), hTa]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kp₃ 224 (.inr ⟨by decide, by decide⟩)]; exact htl
  have q₁ := he₃.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₃.rd ++ s₃.wr) (SP + BitVec.ofNat 64 16) 8 := by rw [hrd₃, hwr₃]; exact hTar
  obtain ⟨s₄, run₄, hbx₄, hsi₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 16))] s₃ = some s₄ ∧ s₄.gpr .rbx = BitVec.ofNat 64 t ∧ s₄.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [he₃.r15, he₃.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₃]
    · simp [gpr_setReg, hTa₃]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- The received tag, padded.
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr (recv_ok he₄ hbx₄ h1 h16 hsi₄
    (by rw [hrd₄, hrd₃, hwr₄, hwr₃]; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₅ ⟨⟨he₅, hr₅, f₅, hbx₅⟩, hrd₅, hwr₅⟩ => ?_)
  rw [hbx₄] at hbx₅
  refine WP.seq (WP.mono (AesGcm.X86_64.WP.with_rdwr
    (cmp_ok La (o := 112) (.inr rfl) he₅ hbx₅ h1 h16 (length_bytesAt _ _ _) hr₅))
    fun s₆ ⟨⟨he₆, hax₆, f₆⟩, hrd₆, hwr₆⟩ => ?_)
  have d256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact La.w_w (.inl (by decide)) (by decide) (by decide)
  have hU : bytesAt s₅.mem (W + BitVec.ofNat 64 112) t = T.take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₅ d256 (by decide), hm₄, hT₃]
  rw [hU, hm₄, hTp₃, ite_ofNat] at hax₆
  generalize hk : (if T.take t = bytesAt s.mem Tp t then 1 else 0) = k at hax₆
  have hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  have w₇ := he₆.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₇, run₇, hz₇, hg₇, hm₇, hrd₇, hwr₇⟩ : ∃ s₇, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₆ = some s₇ ∧ s₇.zf = some (decide (k = 0)) ∧ (∀ r, s₇.gpr r = s₆.gpr r) ∧
      s₇.mem = s₆.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by xrun [he₆.r15, w₇], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₆, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₆]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇ := he₆.keep (fun r _ => hg₇ r) hrd₇ hwr₇
  have g₇ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩]
      s₃.mem s₇.mem := by
    have g₅ := f₅.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have g₆ := f₆.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    rw [hm₄] at g₅
    rw [hm₇]
    exact (g₅.trans g₆).writeW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  have f₇ : Frame (wFrame W SP) s₃.mem s₇.mem := g₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  have F₇ : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s₇.mem := f₃.trans (wFrame_cons f₇)
  have hcb₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [VG.Proof.AesGcm.X86_64.add_ofNat_assoc]
      rcases hr with rfl | rfl | rfl <;> exact La.w_w (.inl (by decide)) (by decide) (by decide)), hcb₃]
  have hj₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = inc32 J := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact La.w_w (.inl (by decide)) (by decide) (by decide)), hj₃, hj]
  have hrd₇' : s₇.rd = s.rd := hrd₇.trans (hrd₆.trans (hrd₅.trans (hrd₄.trans hrd₃)))
  have hwr₇' : s₇.wr = s.wr := hwr₇.trans (hwr₆.trans (hwr₅.trans (hwr₄.trans hwr₃)))
  have hax₇ : s₇.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₇, Mem.readW_writeW_self64]
  subst hk hT
  exact ⟨he₇, F₇, hrd₇', hwr₇', hcb₇, hz₇, hax₇, hj₇⟩

omit v in
/-- After the comparison: the data decrypted if the tags match (`k ≠ 0`), and
the result. -/
theorem openEnd_ok {n k : Nat} {D : Addr} {J : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (hz : s.zf = some (decide (k = 0))) (hax : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hcb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J) :
    WP isa (.seq (.ite .e (.block []) oneCrypt) (.block [.mov .rax (.mem (at_ .r15 auxO))])) s
      fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (oneFrame W D SP n) s.mem s'.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rax = BitVec.ofNat 64 k ∧
        bytesAt s'.mem D n = if k = 0 then bytesAt s.mem D n
          else xorKs (ciphOf s.mem Ctx) (inc32 J) 0 (bytesAt s.mem D n) := by
  have La := L.lay
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧
      Frame (oneFrame W D SP n) s.mem s₈.mem ∧ s₈.rd = s.rd ∧ s₈.wr = s.wr ∧
      s₈.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      bytesAt s₈.mem D n = if k = 0 then bytesAt s.mem D n
        else xorKs (ciphOf s.mem Ctx) (inc32 J) 0 (bytesAt s.mem D n))
    (WP.ite (decide (k = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)) fun s₈ h₈ => ?_)
  · -- The tags differ: the data as it was.
    have h0 : k = 0 := by simpa using ht
    exact WP.block_nil ⟨he, Frame.refl _ _, rfl, rfl, hax, by simp only [h0, ↓reduceIte]⟩
  · -- The tags match: the data decrypted.
    have h0 : k ≠ 0 := by simpa using hf
    refine WP.mono (oneCrypt_ok L (icb := inc32 J) (P := 0) rfl he hdat hlen hd)
      fun s₈ ⟨cr, rd₈, wr₈⟩ => ⟨cr.env, crFrame_one cr.frame, rd₈, wr₈, ?_, ?_⟩
    · rw [cr.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.dw.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact (La.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm
    · simp only [h0, ↓reduceIte]
      exact cr.out (Proof.Gcm.ctr_zero _ _ _ _ hcb)
  obtain ⟨he₈, f₈, hrd₈, hwr₈, hax₈, hD₈⟩ := h₈
  have q₉ := he₈.perm.wR (show 216 + 8 ≤ 2560 by decide)
  refine WP.run (Q := fun s₉ => s₉.gpr .rax = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rax → s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr)
    ⟨_, by xrun [he₈.r15, q₉], by simp [gpr_setReg, hax₈], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
    fun s₉ ⟨hax₉, hg₉, hm₉, hrd₉, hwr₉⟩ => ?_
  exact ⟨he₈.keep (fun r hr => hg₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₉ hwr₉, by rw [hm₉]; exact f₈,
    by rw [hrd₉, hrd₈], by rw [hwr₉, hwr₈], hax₉, by rw [hm₉]; exact hD₈⟩

end

/-- What `open` returns and leaves in the data, as `openResult` says. -/
abbrev OpenRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0 ∧ bytesAt s.mem D n = c

/-- What `open` leaves before the exit, for a tag length it allows. -/
abbrev OpenOkPost (s : State) (Ctx W SP Np A D T : Addr) (nl al n t : Nat) (s₅ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧ s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧
    OpenRes (ctxCiph s.mem Ctx) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem D n)
      (bytesAt s.mem A al) (bytesAt s.mem T t) D n s₅

/-- `open`'s body for a tag length it allows, after the entry: `oneAad`, the
tags compared, and the data decrypted if they match. -/
theorem openOk_ok (v : GcmImpl) {s s₂ : State}
    {Ctx W SP Np A D T : Addr} {nl al n t : Nat} (C : OneCtx s 4 Ctx W SP Np A D nl al n)
    (E : OneEntry s Ctx W SP A D n s₂)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al)
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTr : Covers [⟨T, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨T, t⟩)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩)
    (htl : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (hok' : Spec.Gcm.tagLenOk t = true) :
    WP isa (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (.block []) oneCrypt)
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))) s₂
      (OpenOkPost s Ctx W SP Np A D T nl al n t) := by
  have L := C.lay
  have La := L.lay
  have hlt := C.data.dw.ok.lt
  unfold OpenOkPost
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
    omega_arith
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ M => ?_)
  generalize hH : ctxH s.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s.mem A al = a at M ⊢
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal' : a.length = al := by rw [← ha, length_bytesAt]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), htl]
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = T := by
    rw [M.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr fun _ h => h))) (by decide), hTa]
  have hx16 : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hd₃ : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s₃ D n := C.data.of_eq M.rd M.wr
  refine AesGcm.X86_64.WP.seq5 (openCheck_ok v L (al := al) hx16 M.env M.hH M.dat M.len M.tlen hlt hal₃ htl₃
    hb.1 hb.2 hd₃.dw.ok C.dE C.data.dw.ctx M.abs M.j0 hTa₃ (by rw [M.rd, M.wr]; exact hTar)
    (by rw [M.rd, M.wr]; exact hTr) oT.ws oA.ws) fun s₄ O => ?_
  rw [padded_eq] at O
  generalize hk : (if (toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s₃.mem D n))))
    [ofBytes (lensBlock al n)] ^^^ ciphOf s₃.mem Ctx (Spec.Gcm.j0 H iv))).take t = bytesAt s₃.mem T t then 1 else 0) = k
    at O
  have fO := wFrame_one (D := D) (n := n) (.inr rfl) O.frame
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => fO.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd')
      (by decide)
  have dO : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.stk.symm
  have hp₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n := bytesAt_frame O.frame dO (by omega_arith)
  have dC : ∀ r ∈ oneFrame W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact La.cw'.sub_right (Region.sub_prefix (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact C.data.dw.ctx
    · exact L.kc.symm
  have hc₄ : ciphOf s₄.mem Ctx = ciphOf s₃.mem Ctx := ciph_frame fO dC
  refine WP.mono (openEnd_ok L (k := k) (J := Spec.Gcm.j0 H iv) O.env
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact M.dat) (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact M.len)
    (C.data.of_eq (O.rd.trans M.rd) (O.wr.trans M.wr)) O.zf O.aux (by rw [O.cb]; exact M.cb))
    fun s₅ ⟨he₅, f₅, _, _, hax₅, hD₅⟩ => ?_
  rw [hc₄, hp₄] at hD₅
  -- From the entry to `s₃`.
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₃ : ciphOf s₃.mem Ctx = ctxCiph s.mem Ctx := ciph_frame M.frame (fun r hr => dM _ _ La.cw' L.kc r hr)
  have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.stk) (by omega_arith)
  have hw₃ : bytesAt s₃.mem T t = bytesAt s.mem T t := bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact oT _ (.inl fun _ h => h)
    · exact oT _ (.inr (.inr fun _ h => h))) (by omega_arith)
  have dRet : ∀ r ∈ oneFrame W D SP n, (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.rW.sub_right (Region.sub_prefix (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rD
    · exact ret_stk SP
  refine ⟨he₅, (M.saved.frame fO (saved_oneFrame L C.dE)).frame f₅ (saved_oneFrame L C.dE), ?_, ?_⟩
  · rw [ret_kept f₅ dRet, ret_kept fO dRet, ret_kept M.frame (fun r hr => ?_)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact C.rW
    · exact ret_stk SP
  · rw [hc₃, hp₃, hw₃] at hk
    rw [hc₃, hp₃, ← Proof.Gcm.gctr_eq] at hD₅
    subst hk
    simp only [OpenRes, Spec.Gcm.openResult, hok', ↓reduceIte, Spec.Gcm.decryptWith,
      Proof.Gcm.fullTag_eq, length_bytesAt, hal']
    by_cases e : List.take t (toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ctxCiph s.mem Ctx (Spec.Gcm.j0 H iv))) = bytesAt s.mem T t
    · simp only [e, ↓reduceIte, Nat.one_ne_zero] at hD₅ hax₅ ⊢; exact ⟨hax₅, hD₅⟩
    · simp only [e, ↓reduceIte] at hD₅ hax₅ ⊢; exact ⟨hax₅, hD₅⟩

/-- `vg_sm4_gcm_open`. -/
theorem open_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.openX86_64.pre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.openX86_64.post s s' := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  have hTar := C.args 1 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hnl : (s.gpr .rdx).toNat = nl at *
  generalize hA : s.gpr .rcx = A at *
  generalize hal : (s.gpr .r8).toNat = al at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  generalize hT : stackArg s 1 = T at *
  generalize hW : stackArg s 3 = W at *
  have L := C.lay
  refine WP.seq (WP.mono (openEntry_ok C hCtx hSP hA hD hn hW') fun s₁ ⟨E, hbx₁, htl₁, fE⟩ => ?_)
  generalize ht : (stackArg s 2).toNat = t at hTr d_td d_tw t_t ⊢
  have oT : OutWDS W D SP n ⟨T, t⟩ := fun r hr =>
    hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun r hr => arg16_disj (by decide) C.dA C.dAD hr
  have hbx₁' : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hbx₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₁' : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [htl₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁' (ht ▸ (stackArg s 2).isLt)) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  have E₂ : OneEntry s Ctx W SP A D n s₂ := E.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  have dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  have dDR : ∀ r ∈ [oneR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (Q := OpenOkPost s Ctx W SP Np A D T nl al n t)
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₂) (fun hbad => ?_) (fun hok => ?_)) fun s₅ h₅ => ?_)
  · -- A length `tagLenOk` does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₅ => s₅.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₅.gpr r = s₂.gpr r) ∧ s₅.mem = s₂.mem ∧
        s₅.rd = s₂.rd ∧ s₅.wr = s₂.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₅ ⟨hax, hg₅, hm₅, hrd₅, hwr₅⟩ => ?_
    refine ⟨E₂.env.keep (fun r hr => hg₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅, by rw [hm₅]; exact E₂.saved, ?_, ?_⟩
    · rw [hm₅, k₂.mem, ret_kept fE dR]
    · simp only [OpenRes, Spec.Gcm.openResult, hbad', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hax, by rw [hm₅, k₂.mem, bytesAt_frame fE dDR (by omega_arith)]⟩
  · -- An allowed length.
    exact openOk_ok v C E₂ hNp hnl hal hTa hTar hTr oT oA (by rw [k₂.mem]; exact htl₁') (by simpa using hok)
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨hg, hm, hax⟩ => ⟨hg, ?_⟩
  simp only [Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, ht]
  simp only [OpenRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩

end VG.Proof.Sm4Gcm.X86_64
