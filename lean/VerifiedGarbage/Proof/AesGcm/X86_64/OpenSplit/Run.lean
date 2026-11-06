module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `open_split` on x86-64: correctness

Untrusted: everything here is checked by Lean. `open_split`'s precondition
gives `open`'s context (`OneCtx`, for its six arguments on the stack), where
`src` and the received tag are and what they are apart from (`OSCtx`). The
entry leaves what `open`'s does (`OneEntry`), with `src` and `len` kept at
`tlO` and `tlenO` (`entryS_ok`); after `J₀` and the additional data
(`oneMid_ok`), `seal_split`'s `prefix` decrypts the whole blocks at `src` to
`dst` and copies the bytes left (`OpenSplit.prefixD_ok`), from which `open`'s
tag of the ciphertext is compared with the received one (`openCheckA_ok`),
and the bytes left decrypted if they match (`endS_ok`): `open` of the
ciphertext at `src` (`openSplitM_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split (PP stk56_sub)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ghash blocks ofBytes toBytes zeros
  padLen gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

/-- What `open_split`'s precondition gives: `open`'s context, for the data
`D` (`dst`) of `n` (`len`) bytes, the `n` bytes at `S` (`src`) and the `t`
bytes of the received tag at `T`, apart from what is written, and the 56
bytes below the stack pointer apart from the buffers. -/
structure OSCtx (s : State) (cl : Nat) (Ctx W SP Np A D S T : Addr) (nl al n t : Nat) : Prop
    extends OneCtx s 7 Ctx W SP Np A D nl al n where
  src : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  sW : (⟨S, n⟩ : Region).Disjoint ⟨W, 2560⟩
  sD : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩
  sWrap : S.toNat + n ≤ 2 ^ 64
  kM : (below SP 56).Disjoint ⟨Ctx, cl⟩
  kw : (below SP 56).Disjoint ⟨W, 2560⟩
  kd : (below SP 56).Disjoint ⟨D, n⟩
  ks : (below SP 56).Disjoint ⟨S, n⟩
  sp56 : 56 ≤ SP.toNat
  tag : Covers [⟨T, t⟩] (s.rd ++ s.wr)
  tD : (⟨T, t⟩ : Region).Disjoint ⟨D, n⟩
  tW : (⟨T, t⟩ : Region).Disjoint ⟨W, 2560⟩
  tK : (below SP 56).Disjoint ⟨T, t⟩

theorem OSCtx.of {cl : Nat} {s : State} (hp : Proof.AesGcm.openSplitPre cl s) (hcl : 256 ≤ cl) :
    OSCtx s cl (s.gpr .rdi) (stackArg s 6) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0) (stackArg s 4)
      (stackArg s 2) (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat (stackArg s 3).toNat := by
  have hp' := hp
  simp only [Proof.AesGcm.openSplitPre, Proof.AesGcm.stk56, Proof.AesGcm.args, Proof.AesGcm.arg] at hp'
  obtain ⟨hrd, hwr, hl, d_td, d_tw, t_t, -, s_d, s_w, k_c, -, -, k_s, k_d, k_w, ws, sp56, -⟩ := hp'
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd
  refine ⟨OneCtx.of (w := 6) hl hcl ?_ ?_ ?_ ?_ ?_ ?_, ?_, s_w, s_d, ws, k_c, k_w, k_d, k_s, sp56, ?_, d_td, d_tw,
    t_t⟩
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

/-- From `open_split`'s precondition, for a key context of kind `M`. -/
theorem CtxExt.ofOS {M : CtxMode} {s : State} (hp : Proof.AesGcm.openSplitPre M.len s) (hok : M.ok s.mem (s.gpr .rdi)) :
    CtxExt M (s.gpr .rdi) (stackArg s 6 + BitVec.ofNat 64 16) (stackArg s 6) (s.gpr .rsp) (stackArg s 0)
      (stackArg s 1).toNat s := by
  simp only [Proof.AesGcm.openSplitPre, Proof.AesGcm.oneLay, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, -, ⟨d_cd, d_cw, -, -, -, -, -, -, -, -, -, t_c, -, -, -, -, wc, -⟩, -⟩ := hp
  exact ⟨wc, d_cw.sub_right (Lay.wSub (by decide)), d_cw, d_cd, t_c,
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)), hok⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `OneEntry`, after code that writes only the total length's slot. -/
theorem OneEntry.keep192 {s₀ s s' : State} {A D : Addr} {n : Nat} (E : OneEntry s₀ Ctx W SP A D n s)
    (hg : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem s'.mem) :
    OneEntry s₀ Ctx W SP A D n s' := by
  have kp : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) h' (by decide)) (by decide)
  refine ⟨E.env.keep (fun r hr => ?_) hrd hwr, ⟨by rw [kp 176 (.inl (by decide)) (by decide)]; exact E.rounds.1,
    E.rounds.2⟩, by rw [kp 232 (.inr (by decide)) (by decide)]; exact E.aad,
    by rw [kp 184 (.inl (by decide)) (by decide)]; exact E.alen, by rw [kp 200 (.inr (by decide)) (by decide)]; exact E.dat,
    by rw [kp 208 (.inr (by decide)) (by decide)]; exact E.len, by rw [hg _ (by simp)]; exact E.r12,
    by rw [hg _ (by simp)]; exact E.rbp, by rw [hg _ (by simp)]; exact E.rsp,
    E.saved.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
    E.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩), hrd.trans E.rd, hwr.trans E.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by simp)

end

/-- The entry of `open_split`: `open`'s, with `src` and `len` kept at `tlO`
and `tlenO`, and the tag length in `rbx`. -/
theorem entryS_ok {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 7 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .r8 = A)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : s.mem.readW (SP + BitVec.ofNat 64 56) 64 = W) :
    WP isa (.block OpenSplit.entry) s
      fun s₁ => OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 3 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 4 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n ∧ Frame [oneR W] s.mem s₁.mem := by
  have L := C.lay
  have a₆ := C.args 6 (by decide)
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW a₆) fun s₁ E => ?_)
  have kA : ∀ i < 7, s₁.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := fun i hi => by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
        rw [show 8 * (i + 1) = 8 + 8 * i by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    simp only [stackArg, stackArgAddr]
  have a₁ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by rw [E.rd, E.wr]; exact C.args 1 (by decide)
  have a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [E.rd, E.wr]; exact C.args 3 (by decide)
  have a₄ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 40) 8 := by rw [E.rd, E.wr]; exact C.args 4 (by decide)
  have k₁ := kA 1 (by decide)
  have k₃ := kA 3 (by decide)
  have k₄ := kA 4 (by decide)
  simp only [show 8 * (1 + 1) = 16 from rfl, show 8 * (3 + 1) = 32 from rfl, show 8 * (4 + 1) = 40 from rfl] at k₁ k₃ k₄
  have w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  have w₂ := E.env.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have sep : Mem.Sep (W + BitVec.ofNat 64 224) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    Offset.sep W (.inr (by decide)) (by have := L.ww; omega_arith) (by have := L.ww; omega_arith)
  have hn' : stackArg s 1 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sA : Mem.Sep (SP + BitVec.ofNat 64 16) (64 / 8) (W + BitVec.ofNat 64 224) (64 / 8) := by
    refine Region.Disjoint.sep (?_ : (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩)
      (Region.contains_self _ _) (Region.contains_self _ _)
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
      rw [show (16 : Nat) = 8 + 8 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    exact (C.dA.sub_left hs).sub_right (Lay.wSub (by omega_arith))
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 32)),
      .mov .rax (.mem (at_ .rsp 40)), .store (at_ .r15 tlO) .rax, .mov .rax (.mem (at_ .rsp 16)),
      .store (at_ .r15 tlenO) .rax] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 3 ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 4)).writeW (W + BitVec.ofNat 64 192)
        (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₁, a₃, a₄, w₁, w₂, k₁, k₃, k₄, hn'], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    · simp only [mem_setReg, gpr_setReg]
      rw [Mem.readW_writeW_sep sA (by decide), k₁, hn']
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 192, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)).writeW
      (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (by simp) _ (Region.contains_self _ _)
  have hg' : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₂.gpr r = s₁.gpr r := fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  -- `OneEntry` through the two writes, in two steps.
  let sM : State := s₁.setMem (s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 4))
  have EM : OneEntry s Ctx W SP A D n sM := E.keep L (fun r _ => rfl) rfl rfl
    ((Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _))
  have E₂ : OneEntry s Ctx W SP A D n s₂ := OneEntry.keep192 L EM (fun r hr => hg' r hr) hrd₂ hwr₂ (by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (by simp) _ (Region.contains_self _ _))
  refine WP.of_runBlock ⟨s₂, run₂, E₂, hbx₂, ?_, by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  · rw [hm₂, Mem.readW_writeW_sep sep (by decide), Mem.readW_writeW_self64]
  · exact E.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- After the comparison: the bytes left decrypted if the tags match
(`k ≠ 0`), nothing if not, and the result. -/
theorem endS_ok {M : CtxMode} (B : BlkFn M) {R k q n' : Nat} {D' : Addr} {icb : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D')
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n') (hn' : n' < 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D' n')
    (hz : s.zf = some (decide (k = 0))) (hax : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hctr : Ctr s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s.mem Ctx R) icb (16 * q)) :
    WP isa (.seq (.ite .e (.block []) (oneCrypt (v.withBlk B))) (.block [.mov .rax (.mem (at_ .r15 auxO))])) s
      fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
        Frame (crFrame (W + BitVec.ofNat 64 16) W SP D' n') s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.gpr .rax = BitVec.ofNat 64 k ∧
        (k ≠ 0 → bytesAt s'.mem D' n' = xorKs (ciphOf s.mem Ctx R) icb (16 * q) (bytesAt s.mem D' n')) := by
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W SP D' n') s.mem s₈.mem ∧ s₈.rd = s.rd ∧ s₈.wr = s.wr ∧
      s₈.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      (k ≠ 0 → bytesAt s₈.mem D' n' = xorKs (ciphOf s.mem Ctx R) icb (16 * q) (bytesAt s.mem D' n')))
    (WP.ite (decide (k = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)) fun s₈ h₈ => ?_)
  · -- The tags differ: nothing.
    have h0 : k = 0 := by simpa using ht
    exact WP.block_nil ⟨he, Frame.refl _ _, rfl, rfl, hax, fun h => absurd h0 h⟩
  · -- The tags match: the bytes left decrypted.
    refine WP.mono (crOk_oneCrypt v L (icb := icb) (P₀ := 16 * q) (by omega_arith) hn' he hR hdat hlen hd trivial)
      fun s₈ ⟨cenv, cframe, rd₈, wr₈, cout⟩ => ⟨cenv, cframe, rd₈, wr₈, ?_, fun _ => cout hctr⟩
    rw [cframe.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
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

/-- The result of `open_split`, from the parts. -/
abbrev OSRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0

/-- What `open_split` leaves before the exit, for a tag length it allows. -/
abbrev OSPost (s : State) (Ctx W SP Np A D S T : Addr) (nl al n t : Nat) (s' : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ SavedAt s'.mem W s ∧ s'.mem.readW SP 64 = s.mem.readW SP 64 ∧
    OSRes (ctxCiph s.mem Ctx (s.gpr .rsi).toNat) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem S n)
      (bytesAt s.mem A al) (bytesAt s.mem T t) D n s'

/-- The code of `open_split` after the tag length is checked. -/
abbrev midS (c : Callees) (fFrom : Fn) : Prog isa :=
  .seq (oneAad c)
  (.seq (SealSplit.prefix fFrom)
  (.seq (.block OpenSplit.tagLen)
  (.seq (oneTag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block []) (oneCrypt c))
    (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))))

/-- The tag of `open_split`'s ciphertext compared with the received one:
1 if they match, 0 if not. -/
abbrev osK (s₀ : State) (Ctx Np A S Tp : Addr) (nl al n t R : Nat) : Nat :=
  if (toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx) (blocks (padded (bytesAt s₀.mem A al)
      (bytesAt s₀.mem S n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))).take t =
    bytesAt s₀.mem Tp t then 1 else 0

/-- What `open_split` leaves after the comparison, from the entry state `s₀`:
`OneS` for the bytes left, the result `osK` in `ZF` and at `W + 216`, the
counter after the whole blocks, their plaintext at `dst`, the bytes left of
the ciphertext after them, and what the exit needs. -/
structure FrontS (M : CtxMode) (s₀ : State) (Ctx W SP Np A D S Tp : Addr) (nl al n t R : Nat) (s : State) :
    Prop where
  one : OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dD : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  zf : s.zf = some (decide (osK s₀ Ctx Np A S Tp nl al n t R = 0))
  aux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (osK s₀ Ctx Np A S Tp nl al n t R)
  ctr : Ctr s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
    (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (16 * (n / 16))
  ciph : ciphOf s.mem Ctx R = ctxCiph s₀.mem Ctx R
  whole : bytesAt s.mem D (16 * (n / 16)) = xorKs (ctxCiph s₀.mem Ctx R)
    (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) 0 (bytesAt s₀.mem S (16 * (n / 16)))
  tail : bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
    bytesAt s₀.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
  saved : SavedAt s.mem W s₀
  ret : s.mem.readW SP 64 = s₀.mem.readW SP 64

/-- The code of `open_split` from the additional data to the comparison. -/
abbrev frontS (c : Callees) (fFrom : Fn) : Prog isa :=
  .seq (oneAad c)
  (.seq (SealSplit.prefix fFrom)
  (.seq (.block OpenSplit.tagLen)
  (.seq (oneTag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
    (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))))

/-- `open_split` after the entry, for a tag length it allows, up to the
comparison: `J₀` and the additional data, the whole blocks decrypted from
`src` to `dst` and the bytes left copied, and the tag of the ciphertext
compared with the received one. -/
theorem frontS_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkFromFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁) (hS₁ : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hN₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (frontS (v.withBlk B) T.fn) s₁ (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R) := by
  have L := C.lay
  have hn := C.data.ok.lt
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_arith
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have b24 : Region.Sub (below SP 24) (below SP 56) := below_sub (by decide) (by decide)
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  -- `J₀` and the additional data.
  refine WP.seq (WP.mono (oneMid_ok v C.toOneCtx E hNp hnl hal) fun s₃ M₃ => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M₃
  generalize hiv : bytesAt s₀.mem Np nl = iv at M₃
  generalize ha : bytesAt s₀.mem A al = a at M₃
  have f₃ : Frame (oneFrame W D SP n) s₁.mem s₃.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₃.fr)
  have k₃ : ∀ d, d = 192 ∨ d = 224 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  have P : PP M Ctx W SP D S R n n s₃ :=
    ⟨M₃.env, L, hR ▸ M₃.rounds, M₃.dat, M₃.len, by rw [k₃ 224 (.inr rfl)]; exact hS₁,
      by rw [k₃ 192 (.inl rfl)]; exact hN₁, C.data.of_eq M₃.rd M₃.wr, by rw [M₃.rd, M₃.wr]; exact C.src,
      C.sW, C.sD, C.sWrap, Nat.le_refl _, C.kw, C.kd, C.ks, C.kM, C.sp56,
      X.keep M₃.rd M₃.wr M₃.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩
  -- The whole blocks at `src`, decrypted to `dst`, and the bytes left copied.
  refine WP.seq (WP.mono (prefixD_ok P T) fun s₄ Q => ?_)
  have F₄ : Frame (Split.ppListG W D SP n) s₃.mem s₄.mem := Q.frame.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have wsl : ∀ d, 128 ≤ d → d + 8 ≤ 200 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L C.dE C.kw (.inr (.inl ⟨h₁, h₂⟩))) (by decide)
  -- The stack arguments: apart from `W`, the data and the stack below `SP`.
  have dArg : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) →
      (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
    intro e h₁ h₂ r hr
    have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
      rw [show e = 8 + (e - 8) by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    rcases hr with hr | hr | hr
    · exact (C.dA.sub_left hs).sub_right hr
    · exact (C.dAD.sub_left hs).sub_right hr
    · exact (Offset.disjoint_below SP (n := 56) (d := e) (k := 8) (by omega_arith)).sub_right hr
  have argPP : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ r ∈ Split.ppListG W D SP n,
      (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
    intro e h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact dArg h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.cb_sub a hc)))
    · exact dArg h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.y_sub a hc)))
    · exact dArg h₁ h₂ (.inr (.inl fun _ h => h))
    · exact dArg h₁ h₂ (.inl Split.sc_w)
    · exact dArg h₁ h₂ (.inl (Lay.wSub (by decide)))
    · exact dArg h₁ h₂ (.inr (.inr fun _ h => h))
  have argM : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 →
      s₄.mem.readW (SP + BitVec.ofNat 64 e) 64 = s₀.mem.readW (SP + BitVec.ofNat 64 e) 64 := fun h₁ h₂ => by
    rw [F₄.readW (Region.contains_self _ _) (argPP h₁ h₂) (by decide),
      M₃.frame.readW (Region.contains_self _ _) (dM (dArg h₁ h₂ (.inl fun _ h => h))
        ((dArg h₁ h₂ (.inr (.inr b8))).symm)) (by decide)]
  -- `tag_len` kept at `tlO`.
  have rd₄ : s₄.rd = s₀.rd := Q.rd.trans M₃.rd
  have wr₄ : s₄.wr = s₀.wr := Q.wr.trans M₃.wr
  have a₃ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 32) 8 := by
    rw [rd₄, wr₄]; exact C.args 3 (by decide)
  have w₁ := Q.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa OpenSplit.tagLen s₄ = some s₅ ∧
      s₅.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₅.gpr r = s₄.gpr r) ∧
      s₅.mem = s₄.mem.writeW (W + BitVec.ofNat 64 224) (BitVec.ofNat 64 t) ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    have e32 := argM (e := 32) (by decide) (by decide)
    refine ⟨_, by simp only [OpenSplit.tagLen]; xrun [Q.env.rsp, Q.env.r15, a₃, w₁, e32, htl], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e32, htl]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, e32, htl]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have f₅ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₄.mem s₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := Q.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅
  have W224 : ∀ {Y : Region}, Y.Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], Y.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have k₅ : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₅.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (W224 (L.w_w (by omega_arith) h' (by decide))) (by decide)
  have rd₅ : s₅.rd = s₀.rd := hrd₅.trans rd₄
  have wr₅ : s₅.wr = s₀.wr := hwr₅.trans wr₄
  -- What the comparison needs.
  have s240 : Region.Sub ⟨Ctx + BitVec.ofNat 64 240, 16⟩ ⟨Ctx, M.len⟩ := Offset.sub_base Ctx (by have := M.ge; omega_arith)
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f₅ (W224 ((X.cw.sub_left s240).sub_right (Lay.wSub (by decide)))),
      blockAt_frame F₄ (Split.pp_outG (X.cw.sub_left s240) (X.cd.sub_left s240) (C.kM.symm.sub_left s240)), M₃.hH]
  have hR₅ : RoundsAt s₅.mem W R :=
    ⟨by rw [k₅ 176 (.inl (by decide)) (by decide), wsl 176 (by decide) (by decide)]; exact (hR ▸ M₃.rounds).1, hR'⟩
  have hdat₅ : s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [k₅ 200 (.inl (by decide)) (by decide)]; exact Q.dat
  have hlen₅ : s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [k₅ 208 (.inl (by decide)) (by decide)]; exact Q.len
  have hN₅ : s₅.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by
    rw [k₅ 192 (.inl (by decide)) (by decide), wsl 192 (by decide) (by decide)]; exact P.slen
  have hal₅ : s₅.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [k₅ 184 (.inl (by decide)) (by decide), wsl 184 (by decide) (by decide), M₃.alen, ← hal,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [hm₅, Mem.readW_writeW_self64]
  have hd₅ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₅ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (C.data.of_eq rd₅ wr₅).drop (by omega_arith)
  have hAl : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hC1l : (bytesAt s₃.mem S (16 * (n / 16))).length % 16 = 0 := by rw [length_bytesAt]; omega_arith
  have yW : Region.Sub (Split.yR W) ⟨W, 2560⟩ := fun a hc => Split.st_w a (Split.y_sub a hc)
  have hy₅ : blockAt s₅.mem (yA W) = ghashFrom H (blockAt s₃.mem (yA W)) (blocks (bytesAt s₃.mem S (16 * (n / 16)))) := by
    rw [blockAt_frame f₅ (W224 (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
      Q.y, Proof.Gcm.blocksAt_eq, ctxH_eq, M₃.hH]
  have habs₅ := Proof.Gcm.absorb_whole M₃.abs hAl hC1l hy₅
  have hj₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [blockAt_frame f₅ (W224 (L.w_w (.inl (by decide)) (by decide) (by decide))),
      blockAt_frame F₄ (Split.pp_wG L C.dE C.kw (d := 16) (k := 16) (.inl (by decide)))]
    exact M₃.j0
  have hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [f₅.readW (Region.contains_self _ _) (W224 (dArg (e := 24) (by decide) (by decide) (.inl (Lay.wSub (by decide)))))
      (by decide), argM (e := 24) (by decide) (by decide), hTa]
  have hTar₅ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by
    rw [rd₅, wr₅]; exact C.args 2 (by decide)
  have hTr₅ : Covers [⟨Tp, t⟩] (s₅.rd ++ s₅.wr) := by rw [rd₅, wr₅]; exact C.tag
  have oT : OutWDS W D SP n ⟨Tp, t⟩ := fun r hr =>
    hr.elim C.tW.sub_right fun h => h.elim C.tD.sub_right fun h => C.tK.symm.sub_right fun x hx => b24 x (h x hx)
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ := fun r hr => arg24_disj (by decide) C.dA C.dAD hr
  have sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega_arith)
  have X₅ : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) s₅ :=
    ((P.ext.keep Q.rd Q.wr F₄ (Split.pp_outG X.cw X.cd C.kM.symm)).keep hrd₅ hwr₅ f₅
      (W224 (X.cw.sub_right (Lay.wSub (by decide))))).sub sD'
  have hX : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega_arith
  -- The tag of the ciphertext, compared with the received one.
  refine WP.mono (openCheckA_ok L (TagOk.toP (tagOk_oneTag v)) pStable_true (M := M)
    (x := a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16))) (N := n) (t := t)
    hX he₅ hH₅ hR₅ hdat₅ hlen₅ hN₅ hn hal₅ htl₅ hb.1 hb.2 hd₅ hd₅.ok.w habs₅ hj₅ hTa₅ hTar₅ hTr₅ oT.ws oA.ws X₅
    (by omega_arith)) fun s₆ MP => ?_
  obtain ⟨M₆, -⟩ := MP
  have hR'₆ := hR'
  have F₆ := wFrame_one (D := D + BitVec.ofNat 64 (16 * (n / 16))) (n := n - 16 * (n / 16)) (.inr rfl) M₆.frame
  have kp₆ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => F₆.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L hd₅.ok.w hd') (by decide)
  have cW : Region.Sub (Split.cbR W) ⟨W, 2560⟩ := fun a hc => Split.st_w a (Split.cb_sub a hc)
  have hcb₆ : blockAt s₆.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      Nat.repeat inc32 (n / 16) (inc32 (Spec.Gcm.j0 H iv)) := by
    rw [M₆.cb, blockAt_frame f₅ (W224 (by rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))]
    exact Q.ctr.trans (congrArg _ M₃.cb)
  have hctr₆ : Ctr s₆.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₆.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) (16 * (n / 16)) :=
    ⟨by rw [hcb₆]; congr 1; omega_arith, fun h => absurd (by omega_arith) h⟩
  -- What the data, the key, the received tag and the ciphertext are at each step.
  have c256 : Region.Sub ⟨Ctx, 256⟩ ⟨Ctx, M.len⟩ := Region.sub_prefix M.ge
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s₀.mem Ctx R :=
    ciph_frame M₃.frame (dM L.cw' ((C.kM.sub_left b8).sub_right c256)) hR'
  have hc₄ : ciphOf s₄.mem Ctx R = ciphOf s₃.mem Ctx R :=
    ciph_frame F₄ (Split.pp_outG L.cw' C.data.ctx (C.kM.sub_right c256).symm) hR'
  have hc₅ : ciphOf s₅.mem Ctx R = ciphOf s₄.mem Ctx R :=
    ciph_frame f₅ (W224 (L.cw'.sub_right (Lay.wSub (by decide)))) hR'
  have hc₆ : ciphOf s₆.mem Ctx R = ciphOf s₅.mem Ctx R :=
    ciph_frame F₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cw'.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact C.data.ctx.sub_right sD'
      · exact L.kc.symm) hR'
  have hS₃ : bytesAt s₃.mem S n = bytesAt s₀.mem S n :=
    bytesAt_frame M₃.frame (dM C.sW (C.ks.sub_left b8)) (by omega_arith)
  have tW : (⟨Tp, t⟩ : Region).Disjoint (below SP 8) := C.tK.symm.sub_right b8
  have hT₅ : bytesAt s₅.mem Tp t = bytesAt s₀.mem Tp t := by
    rw [bytesAt_frame f₅ (W224 (C.tW.sub_right (Lay.wSub (by decide)))) (by omega_arith),
      bytesAt_frame F₄ (Split.pp_outG C.tW C.tD C.tK.symm) (by omega_arith),
      bytesAt_frame M₃.frame (dM C.tW tW.symm) (by omega_arith)]
  have e16 : n % 16 = n - 16 * (n / 16) := by omega_arith
  have tl₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
    rw [bytesAt_frame f₅ (W224 (hd₅.ok.w.sub_right (Lay.wSub (by decide)))) (by omega_arith), ← e16]
    exact Q.tail
  have eT : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16)) ++
      bytesAt s₅.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S n := by
    rw [tl₅, List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hq]
  rw [eT, padded_eq, hc₅, hc₄, hc₃, hT₅, hS₃] at M₆
  -- The whole blocks, as the call left them.
  have whole₄ := (Proof.Gcm.ctr_wholeTo (m := s₃.mem) (m' := s₄.mem) (cb := cbA W) (ks := W) (sp := S) (dp := D)
    (ciph := ciphOf s₃.mem Ctx R) (icb := blockAt s₃.mem (cbA W)) (n := 0) (nb := n / 16)
    ⟨rfl, fun h => (h rfl).elim⟩ rfl Q.blocks Q.ctr).1
  rw [hc₃, show blockAt s₃.mem (cbA W) = inc32 (Spec.Gcm.j0 H iv) from M₃.cb] at whole₄
  have dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.ok.stk.symm
  have tail₆ : bytesAt s₆.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
    rw [bytesAt_frame M₆.frame (fun r hr => (dD r hr).sub_left sD') (by omega_arith), tl₅]
  have hcc : ciphOf s₀.mem Ctx R = ctxCiph s₀.mem Ctx R := rfl
  rw [hcc] at M₆ whole₄
  -- The return address and the saved registers, kept.
  have rS : ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) → (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact C.rW.sub_right hr
    · exact C.rD.sub_right hr
    · exact (Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)).sub_right hr
  have hA₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (.inr ⟨by decide, by decide⟩)) (by decide)]; exact E.aad
  have hA₅ : s₅.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
    rw [k₅ 232 (.inr (by decide)) (by decide), F₄.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L C.dE C.kw (.inr (.inr ⟨by decide, by decide⟩))) (by decide)]; exact hA₃
  have X₆ := X₅.keep M₆.rd M₆.wr M₆.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm)
  subst hH hiv ha
  refine ⟨⟨M₆.env, ⟨by rw [kp₆ 176 (.inl ⟨by decide, by decide⟩)]; exact hR₅.1, hR'⟩,
    by rw [kp₆ 232 (.inr ⟨by decide, by decide⟩)]; exact hA₅,
    by rw [kp₆ 184 (.inl ⟨by decide, by decide⟩)]; exact hal₅,
    by rw [kp₆ 200 (.inl ⟨by decide, by decide⟩)]; exact hdat₅,
    by rw [kp₆ 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₅,
    C.aad.of_eq (M₆.rd.trans rd₅) (M₆.wr.trans wr₅), hd₅.of_eq M₆.rd M₆.wr,
    fun N hN => by cases hN; rw [kp₆ 192 (.inl ⟨by decide, by decide⟩)]; exact hN₅, X₆⟩,
    M₆.rd.trans rd₅, M₆.wr.trans wr₅, C.data.of_eq (M₆.rd.trans rd₅) (M₆.wr.trans wr₅), M₆.zf, M₆.aux,
    hctr₆, by rw [hc₆, hc₅, hc₄, hc₃]; rfl, ?_, ?_, ?_, ?_⟩
  · rw [bytesAt_frame M₆.frame (fun r hr => (dD r hr).sub_left (Region.sub_prefix hq)) (by omega_arith),
      bytesAt_frame f₅ (W224 ((C.dE.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by decide))))
        (by omega_arith), whole₄, bytesAt_frame M₃.frame (dM (C.sW.sub_left (Region.sub_prefix hq))
          ((C.ks.sub_left b8).sub_right (Region.sub_prefix hq))) (by omega_arith)]
  · rw [tail₆]
    exact bytesAt_frame M₃.frame (dM (C.sW.sub_left (Offset.sub_base S (by omega_arith)))
      ((C.ks.sub_left b8).sub_right (Offset.sub_base S (by omega_arith)))) (by omega_arith)
  · exact (((M₃.saved.frame F₄ (Split.pp_wG L C.dE C.kw (d := 128) (k := 48)
      (.inr (.inl ⟨Nat.le_refl _, by decide⟩)))).frame f₅ (W224 (L.w_w (.inl (by decide)) (by decide) (by decide)))).frame
      F₆ (saved_oneFrame L hd₅.ok.w))
  · rw [ret_kept M₆.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inr (.inr b8))),
      ret_kept f₅ (W224 (rS (.inl (Lay.wSub (by decide))))),
      ret_kept F₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact rS (.inl cW)
        · exact rS (.inl yW)
        · exact rS (.inr (.inl fun _ h => h))
        · exact rS (.inl Split.sc_w)
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inr (.inr fun _ h => h))),
      ret_kept M₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact rS (.inl fun _ h => h)
        · exact rS (.inr (.inr b8)))]

theorem WP.seq8 {a b c d e f g h T : Prog isa} {s : State} {P Q : State → Prop}
    (hw : WP isa (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g h))))))) s P)
    (k : ∀ s', P s' → WP isa T s' Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g (.seq h T)))))))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp hw) fun _ hw => WP.seq (WP.mono (WP.seq_iff.mp hw) fun _ hw =>
    WP.seq6 hw k))

/-- `open_split` after the entry, for a tag length it allows: `frontS`, then
the bytes left decrypted if the tags match. -/
theorem midS_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkFromFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁) (hS₁ : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hN₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (midS (v.withBlk B) T.fn) s₁ (OSPost s₀ Ctx W SP Np A D S Tp nl al n t) := by
  have L := C.lay
  have hn := C.data.ok.lt
  unfold OSPost
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega_arith)
  refine WP.seq8 (frontS_ok v B T C X E hS₁ hN₁ hNp hnl hal hR hTa htl hok) fun s₆ F => ?_
  refine WP.mono (endS_ok v L B (R := R) (q := n / 16) F.one.env F.one.rounds F.one.dat F.one.len (by omega_arith)
    F.one.dD F.zf F.aux F.ctr) fun s₇ ⟨he₇, f₇, rd₇, wr₇, ax₇, out₇⟩ => ?_
  rw [F.ciph, F.tail] at out₇
  have rS : ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) → (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact C.rW.sub_right hr
    · exact C.rD.sub_right hr
    · exact (Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)).sub_right hr
  have whole₇ : bytesAt s₇.mem D (16 * (n / 16)) = bytesAt s₆.mem D (16 * (n / 16)) :=
    bytesAt_frame f₇ (pre_crFrame F.dD.ok hq) (by omega_arith)
  refine ⟨he₇, F.saved.frame f₇ (saved_crFrame L F.one.dD), ?_, ?_⟩
  · rw [ret_kept f₇ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact rS (.inr (.inl sD'))
        · exact rS (.inl fun a hc => Split.st_w a (Offset.sub_base (W + BitVec.ofNat 64 16) (show 48 + 32 ≤ 80 by decide) a hc))
        · exact rS (.inl (Lay.wSub (by decide)))
        · exact rS (.inr (.inr b8))), F.ret]
  · simp only [OSRes, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
      length_bytesAt]
    simp only [osK] at ax₇ out₇
    split at ax₇
    · next e =>
      simp only [e, ↓reduceIte]
      refine ⟨ax₇, ?_⟩
      have e' := bytesAt_add s₇.mem D (16 * (n / 16)) (n - 16 * (n / 16))
      rw [Nat.add_sub_cancel' hq] at e'
      rw [e', whole₇, F.whole, out₇ (by simp [e]), Proof.Gcm.gctr_eq]
      have e'' := Proof.Gcm.xorKs_append (ctxCiph s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx)
        (bytesAt s₀.mem Np nl))) 0 (bytesAt s₀.mem S (16 * (n / 16)))
        (bytesAt s₀.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [length_bytesAt, Nat.zero_add, ← bytesAt_add, Nat.add_sub_cancel' hq] at e''
      exact e''.symm
    · next e =>
      simp only [e, ↓reduceIte]
      exact ax₇

/-- `vg_aes_gcm_open_split`, for a key context of kind `M`. -/
theorem openSplitM_wp (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkFromFn M) {s : State}
    (hp : (Proof.AesGcm.openSplitX86_64M M).pre s) :
    WP isa (OpenSplit.openSplit (v.withBlk B) T.fn) s
      fun s' => gprPreserved s s' ∧ (Proof.AesGcm.openSplitX86_64M M).post s s' := by
  have X := CtxExt.ofOS hp.1 hp.2
  have C := OSCtx.of hp.1 M.ge
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 56) 64 = stackArg s 6 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have htl : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := rfl
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hD : stackArg s 0 = D at *
  generalize hn : (stackArg s 1).toNat = n at *
  generalize hT : stackArg s 2 = T' at *
  generalize hS : stackArg s 4 = S at *
  generalize hW : stackArg s 6 = W at *
  have L := C.lay
  generalize hR : (s.gpr .rsi).toNat = R at *
  refine WP.seq (WP.mono (entryS_ok C.toOneCtx hCtx hSP hA hD hn hW') fun s₁ ⟨E, hbx₁, hS₁, hN₁, fE⟩ => ?_)
  rw [hS] at hS₁
  generalize ht : (stackArg s 3).toNat = t at C ⊢
  have hst : stackArg s 3 = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hst] at hbx₁ htl
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁ (ht ▸ (stackArg s 3).isLt)) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  have E₂ : OneEntry s Ctx W SP A D n s₂ := E.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  have dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (Q := OSPost s Ctx W SP Np A D S T' nl al n t)
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
    · simp only [OSRes, Spec.Gcm.openResult, hbad', Bool.false_eq_true, ↓reduceIte]
      exact hax
  · -- An allowed length.
    exact midS_ok v B T C X E₂ (by rw [k₂.mem]; exact hS₁) (by rw [k₂.mem]; exact hN₁) hNp hnl hal hTa htl
      (by simpa using hok)
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  rw [hR] at hres
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨hg, hm, hax⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.openSplitX86_64M, Proof.AesGcm.openSplitResult, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, hS, hR, ht]
  simp only [OSRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩
  · next h => rw [h] at hres; rw [hax, hres]; rfl

end VG.Proof.AesGcm.X86_64.OpenSplit
