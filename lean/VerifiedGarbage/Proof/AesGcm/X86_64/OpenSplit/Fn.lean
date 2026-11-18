module

-- separate module: the function's static facts, which need none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToSplit.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Open
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Gcm.StreamTo
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! ### `AesGcm.X86_64.OpenSplit.CT`, which only this module used -/

section

/-! ### `AesGcm.X86_64.OpenSplit.PrefixCT`, which only this module used -/

section

/-!
# AES-GCM `open_split` on x86-64: `prefix` in constant time

Untrusted: everything here is checked by Lean. `OpenSplit.prefix`, as
`Split.prefix_ct` for `seal_split`'s, with the call of
`vg_aes_gcm_decrypt_blocks_to` and no copy (`prefixD_ct`): the same blocks,
checked by the taint analysis, and the same branch on the public length,
with `Mid2D` in place of `Mid2` after the call, which gets the same public
arguments in both runs (`callD_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (step skip_rel)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ : State} (h : PP M Ctx W SP D S R n sl σ)
include h

omit h in
theorem mid2D_zero {s : State} (g : G₁ Ctx W SP sl σ s) (h0 : sl / 16 = 0) : Mid2D Ctx W SP D S R sl σ s := by
  obtain ⟨he, -, -, m, rd, wr⟩ := g
  refine ⟨he, rd, wr, by rw [m]; exact Frame.refl _ _, ?_, ?_, ?_⟩
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl

theorem mid2D_call_wp (T : BlkToDecFn M) {s : State} (g : G₂ Ctx W SP D S R sl σ s) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) s
      (Mid2D Ctx W SP D S R sl σ) := by
  obtain ⟨he, di, si, dx, cx, r8, r9, r10, r11, ax, m, rd, wr⟩ := g
  refine WP.mono (preCallToDec_ok h T (q := sl / 16) (by omega_arith) he.rsp rd wr m di si dx cx r8 r9 r10 r11 ax)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans rd, wr₃.trans wr, by rw [m] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

end

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP M Ctx W SP D S R n sl σ) (h' : PP M Ctx W SP D S R n sl σ')
include h h'

/-- The call of `vg_aes_gcm_decrypt_blocks_to`, in two runs: the same public
arguments. -/
theorem callD_rel (T : BlkToDecFn M) :
    RelCT isa (fun s₁ s₂ => G₂ Ctx W SP D S R sl σ s₁ ∧ G₂ Ctx W SP D S R sl σ' s₂)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le _ _
  refine RelCT.frame (fun _ _ g => by rw [g.1.1.rsp, g.2.1.rsp])
    (RelCT.callEx (k := Proof.AesGcm.decryptBlocksToX86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := hab
  obtain ⟨he₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, r11₁, ax₁, m₁, rd₁, wr₁⟩ := g₁
  obtain ⟨he₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, m₂, rd₂, wr₂⟩ := g₂
  obtain ⟨p₁, cr₁, cw₁, gU₁, hU₁, a0₁, a1₁, a2₁⟩ :=
    callIn h hq he₁.rsp rd₁ wr₁ m₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ r11₁ ax₁
  obtain ⟨p₂, cr₂, cw₂, gU₂, hU₂, a0₂, a1₂, a2₂⟩ :=
    callIn h' hq he₂.rsp rd₂ wr₂ m₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ r11₂ ax₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, cr₁, cw₁, cr₂, cw₂, by rw [pushed_rsp, pushed_rsp, he₁.rsp, he₂.rsp]⟩
  simp only [Proof.AesGcm.decryptBlocksToX86_64M, Proof.AesGcm.blocksToPub, Proof.AesGcm.arg, callU] at *
  simp only [gU₁ _ (by decide : Reg.rdi ≠ .rsp), gU₁ _ (by decide : Reg.rsi ≠ .rsp),
    gU₁ _ (by decide : Reg.rdx ≠ .rsp), gU₁ _ (by decide : Reg.rcx ≠ .rsp), gU₁ _ (by decide : Reg.r8 ≠ .rsp),
    gU₁ _ (by decide : Reg.r9 ≠ .rsp), gU₂ _ (by decide : Reg.rdi ≠ .rsp), gU₂ _ (by decide : Reg.rsi ≠ .rsp),
    gU₂ _ (by decide : Reg.rdx ≠ .rsp), gU₂ _ (by decide : Reg.rcx ≠ .rsp), gU₂ _ (by decide : Reg.r8 ≠ .rsp),
    gU₂ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂, hU₁, hU₂,
    a0₁, a0₂, a1₁, a1₂, a2₁, a2₂, and_self]

/-- `prefix`'s call, from states with the number of whole blocks in `rax`. -/
theorem callPartD_rel (T : BlkToDecFn M) :
    RelCT isa (fun a b => G₀ Ctx W SP sl σ a ∧ G₀ Ctx W SP sl σ' b)
      (.seq (.block SealSplit.preArgs) (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)))
      fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b := by
  refine RelCT.seq (step [.r13, .r14, .r15] preArgs_check (F₁ := G₀ Ctx W SP sl σ) (F₂ := G₀ Ctx W SP sl σ')
    (fun _ _ g r hr => by
      have e₁ := g.1.1; have e₂ := g.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15])
    (fun _ _ g => g) (fun _ g => g₂_wp h g) (fun _ g => g₂_wp h' g)) ?_
  exact (rel_wp (callD_rel h h' T) (fun _ _ g => g) (fun _ g => mid2D_call_wp h T g)
    (fun _ g => mid2D_call_wp h' T g)).mono (fun _ _ g => g) fun _ _ g => g.2

omit h h' in
theorem restS_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block Impl.AesGcm.X86_64.OpenSplit.rest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- After `prefix`'s call (or none): `rest`. -/
theorem restD_rel :
    RelCT isa (fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b)
      (.block Impl.AesGcm.X86_64.OpenSplit.rest) fun _ _ => True :=
  (step [.r15] restS_check (F₁ := Mid2D Ctx W SP D S R sl σ) (F₂ := Mid2D Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [g.1.env.r15, g.2.env.r15])
    (fun _ _ g => g) (fun _ g => restD_ok h g) (fun _ g => restD_ok h' g)).mono (fun _ _ g => g) fun _ _ _ => trivial

/-- `prefix`, in two runs. -/
theorem prefixD_ct (T : BlkToDecFn M) :
    RelCT isa (fun a b => a = σ ∧ b = σ') (Impl.AesGcm.X86_64.OpenSplit.prefix T.fn) fun _ _ => True := by
  have r15 : ∀ {s₁ s₂ : State}, Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ → Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ →
      ∀ r ∈ [Reg.r15], s₁.gpr r = s₂.gpr r := fun e₁ e₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁.r15, e₂.r15]
  unfold Impl.AesGcm.X86_64.OpenSplit.prefix
  refine RelCT.seq (step [.r15] preTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := G₁ Ctx W SP sl σ) (G₂ := G₁ Ctx W SP sl σ')
    (fun _ _ g => by obtain ⟨rfl, rfl⟩ := g; exact r15 h.env h'.env) (fun _ _ g => g)
    (fun _ hs => by rw [hs]; exact g₁_wp h) (fun _ hs => by rw [hs]; exact g₁_wp h')) ?_
  refine RelCT.seq (R := fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b)
    (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2.1, g.2.2.2.1]) ?_ ?_) ?_
  · refine StreamTo.RelCT.of_imp (sl / 16 = 0) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.2.1] at e; simpa using e) fun h0 => ?_
    exact skip_rel fun _ _ g => ⟨mid2D_zero g.1.1 h0, mid2D_zero g.1.2 h0⟩
  · exact (callPartD_rel h h' T).mono (fun _ _ g =>
      ⟨⟨g.1.1.1, g.1.1.2.1, g.1.1.2.2.2⟩, ⟨g.1.2.1, g.1.2.2.1, g.1.2.2.2.2⟩⟩) fun _ _ g => g
  exact restD_rel h h'

end

end VG.Proof.AesGcm.X86_64.OpenSplit

end

end

/-! ### `AesGcm.X86_64.OpenSplit.Run`, which only this module used -/

section

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
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
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
  obtain kp : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
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
  obtain a₆ := C.args 6 (by decide)
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW a₆) fun s₁ E => ?_)
  obtain kA : ∀ i < 7, s₁.mem.readW (SP + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := fun i hi => by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain hs : Region.Sub ⟨SP + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
        rw [show 8 * (i + 1) = 8 + 8 * i by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    simp only [stackArg, stackArgAddr]
  obtain a₁ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by rw [E.rd, E.wr]; exact C.args 1 (by decide)
  obtain a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [E.rd, E.wr]; exact C.args 3 (by decide)
  obtain a₄ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 40) 8 := by rw [E.rd, E.wr]; exact C.args 4 (by decide)
  obtain k₁ := kA 1 (by decide)
  obtain k₃ := kA 3 (by decide)
  obtain k₄ := kA 4 (by decide)
  simp only [show 8 * (1 + 1) = 16 from rfl, show 8 * (3 + 1) = 32 from rfl, show 8 * (4 + 1) = 40 from rfl] at k₁ k₃ k₄
  obtain w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain w₂ := E.env.perm.wW (show 192 + 8 ≤ 2560 by decide)
  obtain sep : Mem.Sep (W + BitVec.ofNat 64 224) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    Offset.sep W (.inr (by decide)) (by have := L.ww; omega_arith) (by have := L.ww; omega_arith)
  obtain hn' : stackArg s 1 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain sA : Mem.Sep (SP + BitVec.ofNat 64 16) (64 / 8) (W + BitVec.ofNat 64 224) (64 / 8) := by
    refine Region.Disjoint.sep (?_ : (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩)
      (Region.contains_self _ _) (Region.contains_self _ _)
    obtain hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
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
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 192, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)).writeW
      (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (by simp) _ (Region.contains_self _ _)
  obtain hg' : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s₂.gpr r = s₁.gpr r := fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  -- `OneEntry` through the two writes, in two steps.
  let sM : State := s₁.setMem (s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 4))
  obtain EM : OneEntry s Ctx W SP A D n sM := E.keep L (fun r _ => rfl) rfl rfl
    ((Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _))
  obtain E₂ : OneEntry s Ctx W SP A D n s₂ := OneEntry.keep192 L EM (fun r hr => hg' r hr) hrd₂ hwr₂ (by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (by simp) _ (Region.contains_self _ _))
  refine WP.of_runBlock ⟨s₂, run₂, E₂, hbx₂, ?_, by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  · rw [hm₂, Mem.readW_writeW_sep sep (by decide), Mem.readW_writeW_self64]
  · exact E.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- The result of `open_split`, from the parts. -/
abbrev OSRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0

theorem osRes_keep {ciph : Block → Block} {H : Block} {t : Nat} {iv c a tag : List Byte} {D : Addr} {n : Nat}
    (s₁ s₂ : State) (h : OSRes ciph H t iv c a tag D n s₁) (hax : s₂.gpr .rax = s₁.gpr .rax)
    (hm : s₂.mem = s₁.mem) : OSRes ciph H t iv c a tag D n s₂ := by
  simp only [OSRes] at h ⊢
  split at h <;> rw [hax] <;> (try rw [hm]) <;> exact h

/-- What `open_split` leaves before the exit, for a tag length it allows. -/
abbrev OSPost (s : State) (Ctx W SP Np A D S T : Addr) (nl al n t : Nat) (s' : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ SavedAt s'.mem W s ∧ s'.mem.readW SP 64 = s.mem.readW SP 64 ∧
    OSRes (ctxCiph s.mem Ctx (s.gpr .rsi).toNat) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem S n)
      (bytesAt s.mem A al) (bytesAt s.mem T t) D n s'

/-- The code of `open_split` after the tag length is checked. -/
abbrev midS (c : Callees) (fToDec : Fn) : Prog isa :=
  .seq (oneAad c)
  (.seq (.seq (OpenSplit.prefix fToDec) (.block OpenSplit.tagLen))
  (.seq (oneTag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block []) (oneCryptG c true))
    (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))

/-- The tag of `open_split`'s ciphertext compared with the received one:
1 if they match, 0 if not. -/
abbrev osK (s₀ : State) (Ctx Np A S Tp : Addr) (nl al n t R : Nat) : Nat :=
  if (toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx) (blocks (padded (bytesAt s₀.mem A al)
      (bytesAt s₀.mem S n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))).take t =
    bytesAt s₀.mem Tp t then 1 else 0

/-- What `open_split` leaves after the comparison, from the entry state `s₀`:
the bytes left at `src` kept as the data, the result `osK` in `ZF` and at
`W + 216`, the counter after the whole blocks, their plaintext at `dst`, and
what the bytes left need to be decrypted to `dst` (`CryptSrc`) and the exit. -/
structure FrontS (M : CtxMode) (s₀ : State) (Ctx W SP Np A D S Tp : Addr) (nl al n t R : Nat) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (n / 16))
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dD : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  src : DataOk (W + BitVec.ofNat 64 16) W SP s (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
  sD : (⟨S + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region).Disjoint
    ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩
  argD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  argR : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8
  zf : s.zf = some (decide (osK s₀ Ctx Np A S Tp nl al n t R = 0))
  aux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (osK s₀ Ctx Np A S Tp nl al n t R)
  ctr : Ctr s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
    (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (16 * (n / 16))
  ciph : ciphOf s.mem Ctx R = ctxCiph s₀.mem Ctx R
  whole : bytesAt s.mem D (16 * (n / 16)) = xorKs (ctxCiph s₀.mem Ctx R)
    (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) 0 (bytesAt s₀.mem S (16 * (n / 16)))
  tail : bytesAt s.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
    bytesAt s₀.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
  saved : SavedAt s.mem W s₀
  ret : s.mem.readW SP 64 = s₀.mem.readW SP 64

/-- The code of `open_split` from the additional data to the comparison. -/
abbrev frontS (c : Callees) (fToDec : Fn) : Prog isa :=
  .seq (oneAad c)
  (.seq (.seq (OpenSplit.prefix fToDec) (.block OpenSplit.tagLen))
  (.seq (oneTag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
    (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))

/-- `open_split` after the entry, for a tag length it allows, up to the
comparison: `J₀` and the additional data, the whole blocks decrypted from
`src` to `dst` and the bytes left copied, and the tag of the ciphertext
compared with the received one. -/
theorem frontS_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁) (hS₁ : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hN₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hDa : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (frontS (v.withBlk B) T.fn) s₁ (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R) := by
  have L := C.lay
  have hn := C.data.ok.lt
  obtain hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  obtain hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_arith
  obtain hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  obtain b24 : Region.Sub (below SP 24) (below SP 56) := below_sub (by decide) (by decide)
  obtain dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
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
  obtain f₃ : Frame (oneFrame W D SP n) s₁.mem s₃.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₃.fr)
  obtain k₃ : ∀ d, d = 192 ∨ d = 224 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  obtain P : PP M Ctx W SP D S R n n s₃ :=
    ⟨M₃.env, L, hR ▸ M₃.rounds, M₃.dat, M₃.len, by rw [k₃ 224 (.inr rfl)]; exact hS₁,
      by rw [k₃ 192 (.inl rfl)]; exact hN₁, C.data.of_eq M₃.rd M₃.wr, by rw [M₃.rd, M₃.wr]; exact C.src,
      C.sW, C.sD, C.sWrap, Nat.le_refl _, C.kw, C.kd, C.ks, C.kM, C.sp56,
      X.keep M₃.rd M₃.wr M₃.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩
  -- The whole blocks at `src`, decrypted to `dst`.
  refine WP.seq (WP.seq (WP.mono (prefixD_ok P T) fun s₄ Q => ?_))
  obtain F₄ : Frame (Split.ppListG W D SP n) s₃.mem s₄.mem := Q.frame.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 200, 24⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain wsl : ∀ d, 128 ≤ d → d + 8 ≤ 200 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L C.dE C.kw (.inr (.inl ⟨h₁, h₂⟩))) (by decide)
  -- The stack arguments: apart from `W`, the data and the stack below `SP`.
  obtain dArg : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) →
      (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
    intro e h₁ h₂ r hr
    obtain hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
      rw [show e = 8 + (e - 8) by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    rcases hr with hr | hr | hr
    · exact (C.dA.sub_left hs).sub_right hr
    · exact (C.dAD.sub_left hs).sub_right hr
    · exact (Offset.disjoint_below SP (n := 56) (d := e) (k := 8) (by omega_arith)).sub_right hr
  obtain argPP : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ r ∈ Split.ppListG W D SP n,
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
  obtain argM : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 →
      s₄.mem.readW (SP + BitVec.ofNat 64 e) 64 = s₀.mem.readW (SP + BitVec.ofNat 64 e) 64 := fun h₁ h₂ => by
    rw [F₄.readW (Region.contains_self _ _) (argPP h₁ h₂) (by decide),
      M₃.frame.readW (Region.contains_self _ _) (dM (dArg h₁ h₂ (.inl fun _ h => h))
        ((dArg h₁ h₂ (.inr (.inr b8))).symm)) (by decide)]
  -- `tag_len` kept at `tlO`.
  obtain rd₄ : s₄.rd = s₀.rd := Q.rd.trans M₃.rd
  obtain wr₄ : s₄.wr = s₀.wr := Q.wr.trans M₃.wr
  obtain a₃ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 32) 8 := by
    rw [rd₄, wr₄]; exact C.args 3 (by decide)
  obtain w₁ := Q.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa OpenSplit.tagLen s₄ = some s₅ ∧
      s₅.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₅.gpr r = s₄.gpr r) ∧
      s₅.mem = s₄.mem.writeW (W + BitVec.ofNat 64 224) (BitVec.ofNat 64 t) ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    obtain e32 := argM (e := 32) (by decide) (by decide)
    refine ⟨_, by simp only [OpenSplit.tagLen]; xrun [Q.env.rsp, Q.env.r15, a₃, w₁, e32, htl], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e32, htl]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, e32, htl]
    all_goals rfl
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain f₅ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₄.mem s₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)
  obtain he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := Q.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅
  obtain W224 : ∀ {Y : Region}, Y.Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], Y.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain k₅ : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₅.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (W224 (L.w_w (by omega_arith) h' (by decide))) (by decide)
  obtain rd₅ : s₅.rd = s₀.rd := hrd₅.trans rd₄
  obtain wr₅ : s₅.wr = s₀.wr := hwr₅.trans wr₄
  -- What the comparison needs.
  obtain s240 : Region.Sub ⟨Ctx + BitVec.ofNat 64 240, 16⟩ ⟨Ctx, M.len⟩ := Offset.sub_base Ctx (by have := M.ge; omega_arith)
  obtain hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f₅ (W224 ((X.cw.sub_left s240).sub_right (Lay.wSub (by decide)))),
      blockAt_frame F₄ (Split.pp_outG (X.cw.sub_left s240) (X.cd.sub_left s240) (C.kM.symm.sub_left s240)), M₃.hH]
  obtain hR₅ : RoundsAt s₅.mem W R :=
    ⟨by rw [k₅ 176 (.inl (by decide)) (by decide), wsl 176 (by decide) (by decide)]; exact (hR ▸ M₃.rounds).1, hR'⟩
  obtain hdat₅ : s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [k₅ 200 (.inl (by decide)) (by decide)]; exact Q.dat
  obtain hlen₅ : s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [k₅ 208 (.inl (by decide)) (by decide), Q.len]; congr 1; omega_arith
  obtain hN₅ : s₅.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by
    rw [k₅ 192 (.inl (by decide)) (by decide), wsl 192 (by decide) (by decide)]; exact P.slen
  obtain hal₅ : s₅.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [k₅ 184 (.inl (by decide)) (by decide), wsl 184 (by decide) (by decide), M₃.alen, ← hal,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain htl₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [hm₅, Mem.readW_writeW_self64]
  obtain hd₅ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₅ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (C.data.of_eq rd₅ wr₅).drop (by omega_arith)
  obtain hS₀ : DataOk (W + BitVec.ofNat 64 16) W SP s₀ S n :=
    ⟨C.src, hn, C.sWrap, C.sW.sub_right (Lay.wSub (by decide)), C.sW, C.ks.sub_left b8⟩
  obtain sS : Region.Sub ⟨S + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨S, n⟩ :=
    Offset.sub_base S (by omega_arith)
  obtain hS₅ : DataOk (W + BitVec.ofNat 64 16) W SP s₅ (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (hS₀.of_eq rd₅ wr₅).drop hq
  obtain hAl : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain hC1l : (bytesAt s₃.mem S (16 * (n / 16))).length % 16 = 0 := by rw [length_bytesAt]; omega_arith
  obtain yW : Region.Sub (Split.yR W) ⟨W, 2560⟩ := fun a hc => Split.st_w a (Split.y_sub a hc)
  obtain hy₅ : blockAt s₅.mem (yA W) = ghashFrom H (blockAt s₃.mem (yA W)) (blocks (bytesAt s₃.mem S (16 * (n / 16)))) := by
    rw [blockAt_frame f₅ (W224 (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
      Q.y, Proof.Gcm.blocksAt_eq, ctxH_eq, M₃.hH]
  obtain habs₅ := Proof.Gcm.absorb_whole M₃.abs hAl hC1l hy₅
  obtain hj₅ : blockAt s₅.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [blockAt_frame f₅ (W224 (L.w_w (.inl (by decide)) (by decide) (by decide))),
      blockAt_frame F₄ (Split.pp_wG L C.dE C.kw (d := 16) (k := 16) (.inl (by decide)))]
    exact M₃.j0
  obtain hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [f₅.readW (Region.contains_self _ _) (W224 (dArg (e := 24) (by decide) (by decide) (.inl (Lay.wSub (by decide)))))
      (by decide), argM (e := 24) (by decide) (by decide), hTa]
  obtain hTar₅ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by
    rw [rd₅, wr₅]; exact C.args 2 (by decide)
  obtain hTr₅ : Covers [⟨Tp, t⟩] (s₅.rd ++ s₅.wr) := by rw [rd₅, wr₅]; exact C.tag
  obtain oT : OutWDS W D SP n ⟨Tp, t⟩ := fun r hr =>
    hr.elim C.tW.sub_right fun h => h.elim C.tD.sub_right fun h => C.tK.symm.sub_right fun x hx => b24 x (h x hx)
  obtain oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ := fun r hr => arg24_disj (by decide) C.dA C.dAD hr
  obtain sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega_arith)
  obtain X₅ : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) s₅ :=
    ((P.ext.keep Q.rd Q.wr F₄ (Split.pp_outG X.cw X.cd C.kM.symm)).keep hrd₅ hwr₅ f₅
      (W224 (X.cw.sub_right (Lay.wSub (by decide))))).sub sD'
  obtain hX : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega_arith
  -- The tag of the ciphertext, compared with the received one.
  refine WP.mono (openCheckA_ok L (TagOk.toP (tagOk_oneTag v)) pStable_true (M := M)
    (x := a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16))) (N := n) (t := t)
    hX he₅ hH₅ hR₅ hdat₅ hlen₅ hN₅ hn hal₅ htl₅ hb.1 hb.2 hS₅ hS₅.w habs₅ hj₅ hTa₅ hTar₅ hTr₅ oT.ws oA.ws X₅.ctxOk
    (by omega_arith)) fun s₆ MP => ?_
  obtain ⟨M₆, -⟩ := MP
  have hR'₆ := hR'
  obtain F₆ := wFrame_one (D := D + BitVec.ofNat 64 (16 * (n / 16))) (n := n - 16 * (n / 16)) (.inr rfl) M₆.frame
  obtain kp₆ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => F₆.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L hd₅.ok.w hd') (by decide)
  obtain cW : Region.Sub (Split.cbR W) ⟨W, 2560⟩ := fun a hc => Split.st_w a (Split.cb_sub a hc)
  obtain hcb₆ : blockAt s₆.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      Nat.repeat inc32 (n / 16) (inc32 (Spec.Gcm.j0 H iv)) := by
    rw [M₆.cb, blockAt_frame f₅ (W224 (by rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))]
    exact Q.ctr.trans (congrArg _ M₃.cb)
  obtain hctr₆ : Ctr s₆.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₆.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) (16 * (n / 16)) :=
    ⟨by rw [hcb₆]; congr 1; omega_arith, fun h => absurd (by omega_arith) h⟩
  -- What the data, the key, the received tag and the ciphertext are at each step.
  obtain c256 : Region.Sub ⟨Ctx, 256⟩ ⟨Ctx, M.len⟩ := Region.sub_prefix M.ge
  obtain hc₃ : ciphOf s₃.mem Ctx R = ciphOf s₀.mem Ctx R :=
    ciph_frame M₃.frame (dM L.cw' ((C.kM.sub_left b8).sub_right c256)) hR'
  obtain hc₄ : ciphOf s₄.mem Ctx R = ciphOf s₃.mem Ctx R :=
    ciph_frame F₄ (Split.pp_outG L.cw' C.data.ctx (C.kM.sub_right c256).symm) hR'
  obtain hc₅ : ciphOf s₅.mem Ctx R = ciphOf s₄.mem Ctx R :=
    ciph_frame f₅ (W224 (L.cw'.sub_right (Lay.wSub (by decide)))) hR'
  obtain hc₆ : ciphOf s₆.mem Ctx R = ciphOf s₅.mem Ctx R :=
    ciph_frame F₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cw'.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact C.data.ctx.sub_right sD'
      · exact L.kc.symm) hR'
  obtain hS₃ : bytesAt s₃.mem S n = bytesAt s₀.mem S n :=
    bytesAt_frame M₃.frame (dM C.sW (C.ks.sub_left b8)) (by omega_arith)
  obtain tW : (⟨Tp, t⟩ : Region).Disjoint (below SP 8) := C.tK.symm.sub_right b8
  obtain hT₅ : bytesAt s₅.mem Tp t = bytesAt s₀.mem Tp t := by
    rw [bytesAt_frame f₅ (W224 (C.tW.sub_right (Lay.wSub (by decide)))) (by omega_arith),
      bytesAt_frame F₄ (Split.pp_outG C.tW C.tD C.tK.symm) (by omega_arith),
      bytesAt_frame M₃.frame (dM C.tW tW.symm) (by omega_arith)]
  obtain e16 : n % 16 = n - 16 * (n / 16) := by omega_arith
  obtain tl₅ : bytesAt s₅.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
    rw [bytesAt_frame f₅ (W224 ((C.sW.sub_left sS).sub_right (Lay.wSub (by decide)))) (by omega_arith),
      bytesAt_frame F₄ (Split.pp_outG (C.sW.sub_left sS) (C.sD.sub_left sS) (C.ks.symm.sub_left sS)) (by omega_arith)]
  obtain eT : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S (16 * (n / 16)) ++
      bytesAt s₅.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s₃.mem S n := by
    rw [tl₅, List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hq]
  rw [eT, padded_eq, hc₅, hc₄, hc₃, hT₅, hS₃] at M₆
  -- The whole blocks, as the call left them.
  obtain whole₄ := (Proof.Gcm.ctr_wholeTo (m := s₃.mem) (m' := s₄.mem) (cb := cbA W) (ks := W) (sp := S) (dp := D)
    (ciph := ciphOf s₃.mem Ctx R) (icb := blockAt s₃.mem (cbA W)) (n := 0) (nb := n / 16)
    ⟨rfl, fun h => (h rfl).elim⟩ rfl Q.blocks Q.ctr).1
  rw [hc₃, show blockAt s₃.mem (cbA W) = inc32 (Spec.Gcm.j0 H iv) from M₃.cb] at whole₄
  obtain dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.ok.stk.symm
  obtain dWS : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨S, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.sW.sub_right (Lay.wSub (by decide))
    · exact C.sW.sub_right (Lay.wSub (by decide))
    · exact C.sW.sub_right (Lay.wSub (by decide))
    · exact C.sW.sub_right (Lay.wSub (by decide))
    · exact (C.ks.sub_left b8).symm
  obtain tail₆ : bytesAt s₆.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
    rw [bytesAt_frame M₆.frame (fun r hr => (dWS r hr).sub_left sS) (by omega_arith), tl₅]
  obtain a8 : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact dArg (e := 8) (by decide) (by decide) (.inl (Lay.wSub (by decide)))
    · exact dArg (e := 8) (by decide) (by decide) (.inl (Lay.wSub (by decide)))
    · exact dArg (e := 8) (by decide) (by decide) (.inl (Lay.wSub (by decide)))
    · exact dArg (e := 8) (by decide) (by decide) (.inl (Lay.wSub (by decide)))
    · exact dArg (e := 8) (by decide) (by decide) (.inr (.inr b8))
  have hcc : ciphOf s₀.mem Ctx R = ctxCiph s₀.mem Ctx R := rfl
  rw [hcc] at M₆ whole₄
  -- The return address and the saved registers, kept.
  obtain rS : ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) → (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact C.rW.sub_right hr
    · exact C.rD.sub_right hr
    · exact (Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)).sub_right hr
  obtain hA₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (.inr ⟨by decide, by decide⟩)) (by decide)]; exact E.aad
  obtain hA₅ : s₅.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
    rw [k₅ 232 (.inr (by decide)) (by decide), F₄.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L C.dE C.kw (.inr (.inr ⟨by decide, by decide⟩))) (by decide)]; exact hA₃
  obtain X₆ := X₅.keep M₆.rd M₆.wr M₆.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact X.cw.sub_right (Lay.wSub (by decide))
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm)
  subst hH hiv ha
  refine ⟨M₆.env, ⟨by rw [kp₆ 176 (.inl ⟨by decide, by decide⟩)]; exact hR₅.1, hR'⟩,
    by rw [kp₆ 192 (.inl ⟨by decide, by decide⟩)]; exact hN₅,
    by rw [kp₆ 200 (.inl ⟨by decide, by decide⟩)]; exact hdat₅,
    by rw [kp₆ 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₅,
    M₆.rd.trans rd₅, M₆.wr.trans wr₅, C.data.of_eq (M₆.rd.trans rd₅) (M₆.wr.trans wr₅), hS₅.of_eq M₆.rd M₆.wr,
    (C.sD.sub_left sS).sub_right (Offset.sub_base D (by omega_arith)), ?_,
    by rw [M₆.rd, M₆.wr, rd₅, wr₅]; exact C.args 0 (by decide), M₆.zf, M₆.aux,
    hctr₆, by rw [hc₆, hc₅, hc₄, hc₃]; rfl, ?_, ?_, ?_, ?_⟩
  · rw [M₆.frame.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (w := 64) (Region.contains_self _ _) a8 (by decide),
      f₅.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (w := 64) (Region.contains_self _ _)
        (W224 (dArg (e := 8) (by decide) (by decide) (.inl (Lay.wSub (by decide))))) (by decide),
      argM (e := 8) (by decide) (by decide), hDa]
  · rw [bytesAt_frame M₆.frame (fun r hr => (dD r hr).sub_left (Region.sub_prefix hq)) (by omega_arith),
      bytesAt_frame f₅ (W224 ((C.dE.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by decide))))
        (by omega_arith), whole₄, bytesAt_frame M₃.frame (dM (C.sW.sub_left (Region.sub_prefix hq))
          ((C.ks.sub_left b8).sub_right (Region.sub_prefix hq))) (by omega_arith)]
  · rw [tail₆]
    exact bytesAt_frame M₃.frame (dM (C.sW.sub_left sS) ((C.ks.sub_left b8).sub_right sS)) (by omega_arith)
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

theorem WP.seq7 {a b c d e f g T : Prog isa} {s : State} {P Q : State → Prop}
    (hw : WP isa (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) s P)
    (k : ∀ s', P s' → WP isa T s' Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f (.seq g T))))))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp hw) fun _ hw => WP.seq6 hw k)

/-- The slots of our caller's registers are apart from what `oneCrypt`
writes. -/
theorem saved_crFrame {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {D : Addr} {n : Nat}
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) : ∀ r ∈ crFrame St W SP D n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- `open_split` after the entry, for a tag length it allows: `frontS`, then
`openBody`'s end out of place, the bytes left decrypted from `src` to `dst`
(`oneCryptG`) if the tags match, nothing if not. -/
theorem midS_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁) (hS₁ : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hN₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hDa : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (midS (v.withBlk B) T.fn) s₁ (OSPost s₀ Ctx W SP Np A D S Tp nl al n t) := by
  have L := C.lay
  have hn := C.data.ok.lt
  unfold OSPost
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  obtain hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain sD' : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ :=
    Offset.sub_base D (by omega_arith)
  refine WP.seq7 (frontS_ok v B T C X E hS₁ hN₁ hNp hnl hal hR hTa hDa htl hok) fun s₆ F => ?_
  obtain hdl := F.dD.drop hq
  refine WP.mono (openEndG_ok (Ctx := Ctx) (SP := SP) (rsB := []) (rsG := crFrame (W + BitVec.ofNat 64 16) W SP
      (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))) (Fail := fun _ => True)
      (Good := fun m => bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
        xorKs (ciphOf s₆.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (16 * (n / 16))
          (bytesAt s₆.mem (D + BitVec.ofNat 64 (16 * (n / 16))) 0 ++
            bytesAt s₆.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16) - 0)))
      F.zf F.aux ?_ ?_ (fun _ hr => by simp at hr) ?_) fun s₇ ⟨he₇, rd₇, wr₇, ax₇, hF, hG⟩ => ?_
  · intro _
    exact WP.block_nil ⟨F.env, Frame.refl _ _, rfl, rfl, trivial⟩
  · intro _
    refine WP.mono (oneCryptG_ok v L true (by omega_arith) F.env F.rounds F.dat F.len hdl ?_)
      fun s' ⟨o, rd', wr'⟩ => ⟨o.env, o.frame, rd', wr', o.out F.ctr⟩
    simp only [CryptSrc, ↓reduceIte]
    refine ⟨by omega_arith, F.argR, ?_, F.src, F.sD⟩
    rw [F.argD, F.tlen, ofNat_sub (by omega_arith) hn]
    congr 2; omega_arith
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hdl.ok.w.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  obtain rS : ∀ {r : Region}, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56) → (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    rcases hr with hr | hr | hr
    · exact C.rW.sub_right hr
    · exact C.rD.sub_right hr
    · exact (Offset.base_disjoint_below SP (n := 56) (k := 8) (by decide)).sub_right hr
  obtain rG : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)),
      (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact rS (.inr (.inl sD'))
    · exact rS (.inl fun a hc => Split.st_w a (Offset.sub_base (W + BitVec.ofNat 64 16) (show 48 + 32 ≤ 80 by decide) a hc))
    · exact rS (.inl (Lay.wSub (by decide)))
    · exact rS (.inr (.inr (below_sub (by decide) (by decide))))
  by_cases h0 : osK s₀ Ctx Np A S Tp nl al n t R = 0
  · obtain ⟨f₇, -⟩ := hF h0
    refine ⟨he₇, F.saved.frame f₇ (fun _ hr => by simp at hr), by rw [ret_kept f₇ (fun _ hr => by simp at hr), F.ret], ?_⟩
    simp only [OSRes, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
      length_bytesAt]
    simp only [osK] at h0 ax₇
    split at h0
    · simp at h0
    · next e => simp only [e, ↓reduceIte] at ax₇ ⊢; rw [ax₇]; rfl
  · obtain ⟨f₇, out₇⟩ := hG h0
    refine ⟨he₇, F.saved.frame f₇ (saved_crFrame L hdl.ok.w), by rw [ret_kept f₇ rG, F.ret], ?_⟩
    obtain whole₇ : bytesAt s₇.mem D (16 * (n / 16)) = bytesAt s₆.mem D (16 * (n / 16)) :=
      bytesAt_frame f₇ (pre_crFrame F.dD.ok hq) (by omega_arith)
    rw [F.ciph, show bytesAt s₆.mem (D + BitVec.ofNat 64 (16 * (n / 16))) 0 = [] by simp [bytesAt],
      List.nil_append, Nat.sub_zero, F.tail] at out₇
    simp only [OSRes, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
      length_bytesAt]
    simp only [osK] at h0 ax₇
    split at h0
    · next e =>
      simp only [e, ↓reduceIte] at ax₇ ⊢
      refine ⟨by rw [ax₇]; rfl, ?_⟩
      obtain e' := bytesAt_add s₇.mem D (16 * (n / 16)) (n - 16 * (n / 16))
      rw [Nat.add_sub_cancel' hq] at e'
      rw [e', whole₇, F.whole, out₇, Proof.Gcm.gctr_eq]
      obtain e'' := Proof.Gcm.xorKs_append (ctxCiph s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx)
        (bytesAt s₀.mem Np nl))) 0 (bytesAt s₀.mem S (16 * (n / 16)))
        (bytesAt s₀.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [length_bytesAt, Nat.zero_add, ← bytesAt_add, Nat.add_sub_cancel' hq] at e''
      exact e''.symm
    · exact absurd rfl h0

/-- `vg_aes_gcm_open_split`, for a key context of kind `M`: `openBody` out of
place, around `midS_ok` (`openSkel_ok`). -/
theorem openSplitM_wp (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s : State}
    (hp : (Proof.AesGcm.openSplitX86_64M M).pre s) :
    WP isa (OpenSplit.openSplit (v.withBlk B) T.fn) s
      fun s' => gprPreserved s s' ∧ (Proof.AesGcm.openSplitX86_64M M).post s s' := by
  obtain X := CtxExt.ofOS hp.1 hp.2
  obtain C := OSCtx.of hp.1 M.ge
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 56) 64 = stackArg s 6 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hDa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
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
  generalize ht : (stackArg s 3).toNat = t at C
  obtain hst : stackArg s 3 = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hst] at htl
  obtain ht' : t < 2 ^ 64 := by rw [← ht]; exact (stackArg s 3).isLt
  refine WP.mono (openSkel_ok (E := fun m => m.readW (W + BitVec.ofNat 64 224) 64 = S ∧
      m.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (Res := fun s₅ => OSRes (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem S n)
      (bytesAt s.mem A al) (bytesAt s.mem T' t) D n s₅) C.toOneCtx hSP ht' (fun _ _ h => osRes_keep _ _ h) ?_ ?_ ?_)
    fun s' ⟨hg, hres⟩ => ⟨hg, ?_⟩
  · exact WP.mono (entryS_ok C.toOneCtx hCtx hSP hA hD hn hW') fun s₁ ⟨E, hbx₁, hS₁, hN₁, _⟩ =>
      ⟨E, by rw [hbx₁, hst], by rw [hS₁, hS], hN₁⟩
  · intro hbad s₅ hax _
    simp only [OSRes, Spec.Gcm.openResult, hbad, Bool.false_eq_true, ↓reduceIte]
    exact hax
  · intro s₂ E₂ ⟨hS₂, hN₂⟩ hok
    refine WP.mono (midS_ok v B T C X E₂ hS₂ hN₂ hNp hnl hal hTa hDa htl hok) fun s₅ h₅ => ?_
    simp only [OSPost, hR] at h₅
    exact h₅
  simp only [Proof.AesGcm.openSplitX86_64M, Proof.AesGcm.openSplitResult, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, hS, hR, ht]
  simp only [OSRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hres.1]; rfl, hres.2⟩
  · next h => rw [h] at hres; rw [hres]; rfl

end VG.Proof.AesGcm.X86_64.OpenSplit

end

end

/-!
# AES-GCM `open_split` on x86-64: constant time

Untrusted: everything here is checked by Lean. As `open` (`OpenCT.lean`):
the first branch is on the tag length (public); then both runs go through
`oneAad` (`oneAad_rel`), `seal_split`'s `prefix` with the call of
`vg_aes_gcm_decrypt_blocks_to` (`prefixD_ct`), the tag length kept (the
taint analysis), `oneTag` and the comparison as `open` does. The second
branch is on the comparison, which `open_split` may leak: correctness says it
is whether `openResult` succeeds (`frontS_ok`, `osK_eq`), the same in both
runs by `pub`; then both runs decrypt the bytes left (`oneCrypt`) or not.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split (PP)
open VG.Proof.AesGcm.X86_64.StreamTo (skip_rel)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashFrom ghash blocks ofBytes toBytes inc32)
open VG.Proof.Gcm (xorKs lensBlock padded)

/-- What `open_split`'s entry leaves, for a tag length `t`, after its check. -/
abbrev OpenInS (s₀ : State) (Ctx W SP A D S : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = S ∧ s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n

/-- The tag length, in the argument at `[SP + 32]`, which may be read. -/
abbrev ArgL (SP : Addr) (t : Nat) (s : State) : Prop :=
  s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 32) 8

/-- `osK`, by `openResult`, for a tag length it allows. -/
theorem osK_eq {s₀ : State} {Ctx Np A S Tp : Addr} {nl al n t R : Nat} (hok : Spec.Gcm.tagLenOk t = true) :
    osK s₀ Ctx Np A S Tp nl al n t R = if (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t
      (bytesAt s₀.mem Np nl) (bytesAt s₀.mem S n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome then 1 else 0 := by
  simp only [osK, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

/-- A stack argument between `[SP + 8]` and `[SP + 48]` is apart from `W`,
the data and the 56 bytes below `SP`. -/
theorem argD {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat} (C : OneCtx s 7 Ctx W SP Np A D nl al n)
    {e : Nat} (h₁ : 8 ≤ e) (h₂ : e + 8 ≤ 56) {r : Region}
    (hr : r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56)) :
    (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
    rw [show e = 8 + (e - 8) by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
  rcases hr with hr | hr | hr
  · exact (C.dA.sub_left hs).sub_right hr
  · exact (C.dAD.sub_left hs).sub_right hr
  · exact (Offset.disjoint_below SP (n := 56) (d := e) (k := 8) (by omega_arith)).sub_right hr

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
  {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M)
include L

/-- `OneS`, after code that writes only the tag length's slot. -/
theorem OneS.keep224 {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {Tn : Option Nat} {s s' : State}
    (h : OneS M Ctx W SP R A al D n Tn s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneS M Ctx W SP R A al D n Tn s' := by
  have kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd hd' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) hd' (by decide)) (by decide)
  exact ⟨h.env.keep hg hrd hwr, ⟨by rw [kp 176 (.inl (by decide)) (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr (by decide)) (by decide)]; exact h.aad, by rw [kp 184 (.inl (by decide)) (by decide)]; exact h.alen,
    by rw [kp 200 (.inl (by decide)) (by decide)]; exact h.dat, by rw [kp 208 (.inl (by decide)) (by decide)]; exact h.len,
    h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr, fun N hN => by rw [kp 192 (.inl (by decide)) (by decide)]; exact h.tlen N hN,
    h.ext.keep hrd hwr hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ext.cw.sub_right (Lay.wSub (by decide)))⟩

/-- `J₀` and the additional data, in each run: `OneS`, what `prefix` needs,
and the arguments it keeps. -/
theorem aadS_ok {s₀ s : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (h : OpenInS s₀ Ctx W SP A D S n t s) :
    WP isa (oneAad (v.withBlk B)) s fun s' => (OneS M Ctx W SP R A al D n none s' ∧ PP M Ctx W SP D S R n n s') ∧
      ArgR SP Tp s' ∧ ArgL SP t s' := by
  refine WP.mono (oneMid_ok v C.toOneCtx h.1 hNp hnl hal) fun s₃ M₃ => ?_
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have f₃ : Frame (oneFrame W D SP n) s.mem s₃.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₃.fr)
  have k₃ : ∀ d, d = 192 ∨ d = 224 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  have kA : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 →
      s₃.mem.readW (SP + BitVec.ofNat 64 e) 64 = s₀.mem.readW (SP + BitVec.ofNat 64 e) 64 := fun h₁ h₂ =>
    M₃.frame.readW (Region.contains_self _ _) (dM (argD C.toOneCtx h₁ h₂ (.inl fun _ h => h))
      ((argD C.toOneCtx h₁ h₂ (.inr (.inr b8))).symm)) (by decide)
  refine ⟨⟨(h.1.aadPre C.toOneCtx X hNp hnl hal hR).1.frame L M₃.env (M₃.rd.trans h.1.rd.symm)
      (M₃.wr.trans h.1.wr.symm) C.dE f₃,
    ⟨M₃.env, L, hR ▸ M₃.rounds, M₃.dat, M₃.len, by rw [k₃ 224 (.inr rfl)]; exact h.2.2.1,
      by rw [k₃ 192 (.inl rfl)]; exact h.2.2.2, C.data.of_eq M₃.rd M₃.wr, by rw [M₃.rd, M₃.wr]; exact C.src,
      C.sW, C.sD, C.sWrap, Nat.le_refl _, C.kw, C.kd, C.ks, C.kM, C.sp56,
      X.keep M₃.rd M₃.wr M₃.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩⟩,
    ⟨by rw [ArgT, kA (e := 24) (by decide) (by decide)]; exact hT, by rw [M₃.rd, M₃.wr]; exact C.args 2 (by decide)⟩,
    ⟨by rw [kA (e := 32) (by decide) (by decide)]; exact htl, by rw [M₃.rd, M₃.wr]; exact C.args 3 (by decide)⟩⟩

/-- What stays between the pieces after `prefix`, in each run: `OneT` for the
bytes left at `src`, and the arguments kept. -/
abbrev GB (Ctx W SP : Addr) (R al : Nat) (S : Addr) (n t : Nat) (Tp : Addr) (s : State) : Prop :=
  OneT Ctx W SP R al (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) n s ∧ ArgR SP Tp s ∧ ArgL SP t s

/-- After `prefix`, in each run: `OneT` for the bytes left at `src`, with the
total length, and the arguments it keeps. -/
theorem prefixS_ok {σ : State} {Np A D S Tp : Addr} {s₀ : State} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t)
    (h : (OneS M Ctx W SP R A al D n none σ ∧ PP M Ctx W SP D S R n n σ) ∧ ArgR SP Tp σ ∧ ArgL SP t σ) :
    WP isa (OpenSplit.prefix T.fn) σ (GB Ctx W SP R al S n t Tp) := by
  obtain ⟨⟨O, P⟩, ⟨hT, hTr⟩, ⟨hl, hlr⟩⟩ := h
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hn := P.data.ok.lt
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  refine WP.mono (prefixD_ok P T) fun s Q => ?_
  have F : Frame (Split.ppListG W D SP n) σ.mem s.mem := Q.frame.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 200, 24⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 200) ∨ (224 ≤ d ∧ d + 8 ≤ 448) →
      s.mem.readW (W + BitVec.ofNat 64 d) 64 = σ.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    F.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L P.data.ok.w P.kw (.inr hd)) (by decide)
  have argPP : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ r ∈ Split.ppListG W D SP n,
      (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
    intro e h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact argD C.toOneCtx h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.cb_sub a hc)))
    · exact argD C.toOneCtx h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.y_sub a hc)))
    · exact argD C.toOneCtx h₁ h₂ (.inr (.inl fun _ h => h))
    · exact argD C.toOneCtx h₁ h₂ (.inl Split.sc_w)
    · exact argD C.toOneCtx h₁ h₂ (.inl (Lay.wSub (by decide)))
    · exact argD C.toOneCtx h₁ h₂ (.inr (.inr fun _ h => h))
  have hS : DataOk (W + BitVec.ofNat 64 16) W SP s S n :=
    ⟨by rw [Q.rd, Q.wr]; exact P.srcCov, hn, P.sWrap, P.sW.sub_right (Lay.wSub (by decide)), P.sW, P.ks.sub_left b8⟩
  refine ⟨⟨Q.env, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact O.rounds.1, O.rounds.2⟩,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact O.alen, Q.dat, by rw [Q.len]; congr 1; omega_arith,
    hS.drop hq, by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact P.slen⟩,
    ⟨by rw [ArgT, F.readW (Region.contains_self _ _) (argPP (e := 24) (by decide) (by decide)) (by decide)]; exact hT,
      by rw [Q.rd, Q.wr]; exact hTr⟩,
    ⟨by rw [F.readW (Region.contains_self _ _) (argPP (e := 32) (by decide) (by decide)) (by decide)]; exact hl,
      by rw [Q.rd, Q.wr]; exact hlr⟩⟩

/-- `OneT`, after code that writes only the tag length's slot. -/
theorem OneT.keep224 {R al : Nat} {D : Addr} {n N : Nat} {s s' : State}
    (h : OneT Ctx W SP R al D n N s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneT Ctx W SP R al D n N s' := by
  have kp : ∀ d, d + 8 ≤ 224 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl hd) (by omega_arith) (by decide)) (by decide)
  exact ⟨h.env.keep hg hrd hwr, ⟨by rw [kp 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 184 (by decide)]; exact h.alen, by rw [kp 200 (by decide)]; exact h.dat,
    by rw [kp 208 (by decide)]; exact h.len, h.dD.of_eq hrd hwr, by rw [kp 192 (by decide)]; exact h.tlen⟩

/-- What stays after the tag length is kept at `tlO`, in each run. -/
abbrev GC (Ctx W SP : Addr) (R al : Nat) (S : Addr) (n t : Nat) (Tp : Addr) (s : State) : Prop :=
  OneT Ctx W SP R al (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) n s ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s

/-- The tag length kept at `tlO`, in each run. -/
theorem tagLenS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩) (h : GB Ctx W SP R al S n t Tp s) :
    WP isa (.block OpenSplit.tagLen) s (GC Ctx W SP R al S n t Tp) := by
  have w₁ := h.1.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa OpenSplit.tagLen s = some s₁ ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 224) (BitVec.ofNat 64 t) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [OpenSplit.tagLen]; xrun [h.1.env.rsp, h.1.env.r15, h.2.2.2, w₁, h.2.2.1], ?_, ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, h.2.2.1]
    all_goals rfl
  have f₁ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₁.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₁, run₁, OneT.keep224 L h.1 (fun r hr => hg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd hwr f₁, by rw [hm, Mem.readW_writeW_self64], ?_, ?_⟩
  · have hd : (⟨SP + BitVec.ofNat 64 24, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩ :=
      oA _ (.inl (Lay.wSub (by decide)))
    rw [ArgT, f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)]; exact h.2.1.1
  · rw [hrd, hwr]; exact h.2.1.2

/-- `oneTag` keeps `GC`, in each run. -/
theorem tagS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State} (hn : n < 2 ^ 64)
    (hSW : (⟨S + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region).Disjoint ⟨W, 2560⟩)
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩) (h : GC Ctx W SP R al S n t Tp s) :
    WP isa (oneTag v.callees uO) s (GC Ctx W SP R al S n t Tp) :=
  WP.mono (oneTag_ok v L (o := 112) (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.rounds h.1.dat h.1.len h.1.tlen
    hn h.1.alen h.1.dD hSW) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := S + BitVec.ofNat 64 (16 * (n / 16))) (n := n - 16 * (n / 16)) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hSW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hSW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the address of the received tag into `rsi`. -/
theorem loadTlS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State} (h : GC Ctx W SP R al S n t Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ := h.2.2.2
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2.1]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.env.keep (fun r hr => ?_) hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- From the entry to the comparison, in two runs, for an allowed tag length. -/
theorem frontS_rel {s₀ s₀' : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (C' : OSCtx s₀' M.len Ctx W SP Np A D S Tp nl al n t)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (htl' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) :
    RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (frontS (v.withBlk B) T.fn) fun _ _ => True := by
  have hlt := C.data.ok.lt
  have hSW' := C.sW.sub_left (Offset.sub_base S (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega_arith))
  have oA := C.toOneCtx.arg24 (by decide)
  let GA : State → Prop := fun s => (OneS M Ctx W SP R A al D n none s ∧ PP M Ctx W SP D S R n n s) ∧
    ArgR SP Tp s ∧ ArgL SP t s
  have a := rel_wp ((oneAad_rel v L (R := R) (Np := Np) (nl := nl) (A := A) (al := al) (T := none) C.dE).mono
      (P' := fun (s₁ s₂ : State) => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C.toOneCtx X hNp hnl hal hR, h.2.1.aadPre C'.toOneCtx X' hNp' hnl' hal' hR'⟩)
      fun _ _ _ => trivial) (fun _ _ h => h) (G₁ := GA) (G₂ := GA)
    (fun _ h => aadS_ok v L B C X hNp hnl hal hR hT htl h) (fun _ h => aadS_ok v L B C' X' hNp' hnl' hal' hR' hT' htl' h)
  have b : RelCT isa (fun s₁ s₂ => True ∧ GA s₁ ∧ GA s₂) (OpenSplit.prefix T.fn)
      fun s₁ s₂ => True ∧ GB Ctx W SP R al S n t Tp s₁ ∧ GB Ctx W SP R al S n t Tp s₂ :=
    Split.rel_each fun σ σ' g => (rel_wp (prefixD_ct g.2.1.1.2 g.2.2.1.2 T) (F₁ := (· = σ)) (F₂ := (· = σ'))
      (fun _ _ h => h) (G₁ := GB Ctx W SP R al S n t Tp) (G₂ := GB Ctx W SP R al S n t Tp)
      (fun _ hs => by subst hs; exact prefixS_ok L T C g.2.1)
      (fun _ hs => by subst hs; exact prefixS_ok L T C g.2.2)).mono (fun _ _ h => h) fun _ _ h => h
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ GB Ctx W SP R al S n t Tp s₁ ∧ GB Ctx W SP R al S n t Tp s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.2.1.1.env h.2.2.1.env) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (G₁ := GC Ctx W SP R al S n t Tp) (G₂ := GC Ctx W SP R al S n t Tp)
    (fun _ h => tagLenS_ok L oA.ws h) (fun _ h => tagLenS_ok L oA.ws h)
  have d := rel_wp ((oneTag_relT v L (R := R) (al := al) (N := n) (o := 112) (.inr rfl) hSW').mono
      (P' := fun (s₁ s₂ : State) => True ∧ GC Ctx W SP R al S n t Tp s₁ ∧ GC Ctx W SP R al S n t Tp s₂)
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2)
    (G₁ := GC Ctx W SP R al S n t Tp) (G₂ := GC Ctx W SP R al S n t Tp)
    (fun _ h => tagS_ok v L hlt hSW' oA.ws h) (fun _ h => tagS_ok v L hlt hSW' oA.ws h)
  have e := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧ GC Ctx W SP R al S n t Tp s₁ ∧
      GC Ctx W SP R al S n t Tp s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.1.env h.2.2.1.env) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTlS_ok h) (fun _ h => loadTlS_ok h)
  have f := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩)
    (RelCT.seq (RelCT.seq b c) (RelCT.seq (d.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩) (RelCT.seq e f)))

/-- After the comparison, in two runs with the same result: the bytes left
decrypted from `src` to `dst` if the tags match (`oneCryptG` out of place,
`cryptTailG_rel`), and the result loaded. -/
theorem endS_rel {s₀ s₀' : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (hk : osK s₀ Ctx Np A S Tp nl al n t R = osK s₀' Ctx Np A S Tp nl al n t R) :
    RelCT isa (fun s₁ s₂ => FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
        FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂)
      (.seq (.ite .e (.block []) (oneCryptG (v.withBlk B) true)) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have tb := skip_rel (P := fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
      FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some true)
    (Q := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    fun _ _ h => ⟨h.1.1.env, h.1.2.env⟩
  let D' := D + BitVec.ofNat 64 (16 * (n / 16))
  let S' := S + BitVec.ofNat 64 (16 * (n / 16))
  let n' := n - 16 * (n / 16)
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  -- Each run, after `oneCryptG`'s first block: `CrMid` from its memory then, and `TailSrc`.
  let G : Mem → State → Prop := fun m s₁ => CrMid Ctx (W + BitVec.ofNat 64 16) W SP R 0 0 D' n' m 0 s₁ ∧
    TailSrc true (W + BitVec.ofNat 64 16) W SP s₁ m D' 0 n' S'
  have hB : ∀ {s₀ : State} (s : State), FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s →
      WP isa (.block (oneCryptBlk true)) s fun s₁ => ∃ m, G m s₁ := fun s F => by
    have hn := F.dD.ok.lt
    refine WP.mono (oneCryptBlkTo_ok (R := R) (icb := 0) (P := 0) rfl F.env F.rounds F.dat F.len (F.dD.drop hq) ?_)
      fun s₁ ⟨hm, hts, _⟩ => ⟨_, hm, hts⟩
    simp only [CryptSrc, ↓reduceIte]
    refine ⟨by omega_arith, F.argR, ?_, F.src, F.sD⟩
    rw [F.argD, F.tlen, ofNat_sub (by omega_arith) hn]
    congr 2; omega_arith
  have ts : ∀ {m : Mem} {s₁ : State}, G m s₁ → (true = true → s₁.gpr .rbx = S') := fun h _ => by
    have h2 := h.2; simp only [TailSrc, ↓reduceIte] at h2; exact h2.1
  have hT : ∀ {m : Mem} (s₁ : State), G m s₁ → WP isa (cryptTailG (v.withBlk B) true) s₁
      (Env Ctx (W + BitVec.ofNat 64 16) W SP) := fun _ h =>
    WP.mono (cryptTailG_ok v L true h.1 (by omega_arith) (h.1.ciph L) h.2) fun _ o => o.env
  have eb : RelCT isa (fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
      FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some false) (oneCryptG (v.withBlk B) true)
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
    simp only [oneCryptG, ↓reduceIte]
    have a := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
        FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some false) [.r13, .r14, .r15, .rsp]
        (fun _ _ h => env_agree h.1.1.env h.1.2.env) ⟨_, by taint_decide⟩)
      (fun _ _ h => h.1) (fun s h => hB s h) (fun s h => hB s h)
    refine RelCT.seq a ((RelCT.exists_ (P := fun m₁ s₁ s₂ => G m₁ s₁ ∧ ∃ m, G m s₂) fun m₁ =>
      (RelCT.exists_ (P := fun m₂ s₁ s₂ => G m₁ s₁ ∧ G m₂ s₂) fun m₂ => ?_).mono
        (fun _ _ ⟨h₁, m₂, h₂⟩ => ⟨m₂, h₁, h₂⟩) fun _ _ h => h).mono
      (fun _ _ ⟨_, ⟨m₁, h₁⟩, h₂⟩ => ⟨m₁, h₁, h₂⟩) fun _ _ h => h)
    exact (rel_wp ((cryptTailG_rel v L true (Q := S') (R := R) (icb₁ := 0) (icb₂ := 0)
      (P₁ := 0) (P₂ := 0) (D := D') (n := n') (m₁ := m₁) (m₂ := m₂) (j := 0)).mono
        (P' := fun s₁ s₂ => G m₁ s₁ ∧ G m₂ s₂) (fun _ _ h => ⟨⟨h.1.1, ts h.1⟩, h.2.1, ts h.2⟩) fun _ _ h => h)
      (F₁ := G m₁) (F₂ := G m₂) (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)).mono
        (fun _ _ h => h) fun _ _ h => h.2
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => loadAux_ok h) (fun _ h => loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.1.zf, h.2.zf, hk]) tb eb)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

end

/-- `open_split` after the entry, in two runs with the same result, for an
allowed tag length. -/
theorem midS_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₀' : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (C' : OSCtx s₀' M.len Ctx W SP Np A D S Tp nl al n t)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hDa : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hDa' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (htl' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem S n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem S n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) :
    RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (midS (v.withBlk B) T.fn)
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  have hk : osK s₀ Ctx Np A S Tp nl al n t R = osK s₀' Ctx Np A S Tp nl al n t R := by
    rw [osK_eq hok, osK_eq hok, hres]
  refine rel_reassoc7 (RelCT.seq ?_ (endS_rel v L B (s₀ := s₀) (s₀' := s₀') (Np := Np) (D := D) (S := S) (Tp := Tp)
    (nl := nl) (t := t) hk))
  exact (rel_wp (frontS_rel v L B T C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' htl htl') (fun _ _ h => h)
    (fun _ h => frontS_ok v B T C X h.1 h.2.2.1 h.2.2.2 hNp hnl hal hR hT hDa htl hok)
    (fun _ h => frontS_ok v B T C' X' h.1 h.2.2.1 h.2.2.2 hNp' hnl' hal' hR' hT' hDa' htl' hok)).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- After the entry: the tag length checked, then, if it is allowed, `mid`. -/
theorem openBodyS_relOf {s₀ s₀' : State} {Ctx W SP A D S : Addr} {n t : Nat} {mid : Prog isa}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) (ht : t < 2 ^ 64)
    (hrel : Spec.Gcm.tagLenOk t = true →
      RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂) mid
        fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) :
    RelCT isa (fun s₁ s₂ => True ∧ OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)]) mid))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have hK : ∀ {s₀ s : State}, OpenInS s₀ Ctx W SP A D S n t s → WP isa tagLenOk s fun s' =>
      OpenInS s₀ Ctx W SP A D S n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1],
        by rw [k.mem]; exact h.2.2.1, by rw [k.mem]; exact h.2.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ OpenInS s₀ Ctx W SP A D S n t s₁ ∧
      OpenInS s₀' Ctx W SP A D S n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    exact (hrel hok).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h

/-- `vg_aes_gcm_open_split`, in two runs from states with the same public
values. -/
theorem openSplitM_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.openSplitX86_64M M).pre s₀) (hp' : (Proof.AesGcm.openSplitX86_64M M).pre s₀')
    (hq : (Proof.AesGcm.openSplitX86_64M M).pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (OpenSplit.openSplit (v.withBlk B) T.fn) fun _ _ => True := by
  have X := CtxExt.ofOS hp.1 hp.2
  have X' := CtxExt.ofOS hp'.1 hp'.2
  have C := OSCtx.of hp.1 M.ge
  have C' := OSCtx.of hp'.1 M.ge
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  have hres' : ∀ {s : State}, Proof.AesGcm.rounds s → Proof.AesGcm.openSplitLeak s = [if (Spec.Gcm.openResult
      (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (stackArg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).isSome
      then 1 else 0] := fun h => by
    simp only [Proof.AesGcm.openSplitLeak, Proof.AesGcm.openSplitResult, Proof.AesGcm.arg, h, not_true_eq_false,
      ↓reduceIte]
  rw [hres' C.rounds, hres' C'.rounds] at hres
  have hres := leak_bool hres
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide); have a₄ := qa 4 (by decide); have a₆ := qa 6 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃ a₄ a₆
  have ha₆ := C.args 6 (by decide); have ha₆' := C'.args 6 (by decide)
  have hw56 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 56) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 56) 64 := a₆
  have hT₁ : ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀ := rfl
  have hT₂ : ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀' := by rw [ArgT, q₇, a₂]; rfl
  have hDa₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 := rfl
  have hDa₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 := by rw [q₇, a₀]; rfl
  have htl₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 := rfl
  have htl₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 := by rw [q₇, a₃]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₂, ← a₃, ← a₄, ← a₆] at C'
  rw [← q₁, ← q₇, ← a₀, ← a₁, ← a₆] at X'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₁, ← a₂, ← a₃, ← a₄] at hres
  generalize ht : (stackArg s₀ 3).toNat = t at hres C C'
  have hst : stackArg s₀ 3 = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hst] at htl₁ htl₂
  have hE : ∀ {s : State} (C : OneCtx s 7 (s₀.gpr .rdi) (stackArg s₀ 6) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 56) 64 = stackArg s₀ 6 → stackArg s 3 = stackArg s₀ 3 →
      stackArg s 4 = stackArg s₀ 4 →
      WP isa (.block OpenSplit.entry) s
        (OpenInS s (s₀.gpr .rdi) (stackArg s₀ 6) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 4)
          (stackArg s₀ 1).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => WP.mono (entryS_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, hS, hN, _⟩ =>
      ⟨E, by rw [hbx, h₇, hst], by rw [hS, h₈], hN⟩
  have hE₁ := hE C.toOneCtx rfl rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C'.toOneCtx q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) (by rw [q₇, a₆]; rfl) a₃.symm a₄.symm
  rw [OpenSplit.entry, oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  unfold OpenSplit.openSplit openBody
  rw [OpenSplit.entry, oneEntry]
  simp only [List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 6 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 6) (SP := s₀.gpr .rsp) (k := 56) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) hw56 ha₆ ha₆' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact openBodyS_relOf L (by rw [← ht]; exact (stackArg s₀ 3).isLt) fun hok =>
    midS_rel v B T C C' X X' rfl rfl rfl rfl q₃.symm (by rw [← q₄]) (by rw [← q₆]) (by rw [← q₂]) hT₁ hT₂ hDa₁ hDa₂
      htl₁ htl₂ hres hok

theorem openSplitM_ct (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) :
    ConstantTime isa (Proof.AesGcm.openSplitX86_64M M).pre (Proof.AesGcm.openSplitX86_64M M).pub
      (OpenSplit.openSplit (v.withBlk B) T.fn) :=
  ct_of_rel fun _ _ hp hp' hq => openSplitM_rel v B T hp hp' hq

end VG.Proof.AesGcm.X86_64.OpenSplit

end

end

/-!
# AES-GCM `open_split` on x86-64: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split`
calling any `vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks` `B`
and `vg_aes_gcm_decrypt_blocks_to` `T` loads no `mxcsr`, writes `rsp` only
in its frames and uses 56 bytes of stack (the call's arguments, its return
address and its stack), so it preserves what the ABI says
(`OpenSplitFn.of`): an internal function, which `openToSplit` calls.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M)

theorem openSplit_mx :
    (OpenSplit.openSplit (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, T.mx, OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag,
    oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail,
    flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush, finTag,
    Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openSplit_spAll :
    (OpenSplit.openSplit (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, T.spAll, OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad,
    oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad,
    padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush,
    finTag, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openSplit_xdepth : (OpenSplit.openSplit (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  have e := B.encXd
  have d := B.decXd
  have t := T.xd
  simp only [OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag, oneCrypt,
    oneCryptG, oneCryptBlk, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush,
    lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush, finTag, copyTag,
    copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
    List.length_nil, GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le,
    ↓reduceIte, Bool.false_eq_true]
  omega_using [t]

end

/-- `vg_aes_gcm_open_split`, named `n`, calling `B` and `T`. -/
def _root_.VG.Proof.AesGcm.X86_64.OpenToSplit.OpenSplitFn.of (n : String) (v : GcmImpl) {M : CtxMode} (B : BlkFn M)
    (T : BlkToDecFn M) : OpenToSplit.OpenSplitFn M where
  fn := ⟨n, OpenSplit.openSplit (v.withBlk B) T.fn⟩
  ok s h := by
    obtain ⟨t, s', he, hg, hp⟩ := openSplitM_wp v B T h
    exact ⟨t, s', he, abiPreserved_of_exec (openSplit_mx v B T) he hg, hp⟩
  ct := openSplitM_ct v B T
  sp := SpSafe.of_all (openSplit_spAll v B T)
  xd := openSplit_xdepth v B T
  mx := openSplit_mx v B T
  spAll := openSplit_spAll v B T

end VG.Proof.AesGcm.X86_64.OpenSplit
