module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Cond
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Base

/-!
# AES-GCM `seal_split` on x86-64 with AVX-512: the short path

Untrusted: everything here is checked by Lean. For the instances with
`seal`'s short path, `seal_split` tests the text as `seal` does
(`Short.cond`), and takes `run` for a long one; a short one is copied from
`src` to `dst` first (`copySrc`, by the gathering's `copy`), then sealed there by `Short.sealShort`,
which `Short.sealShort_ok` proves of the state `seal` would have entered
with that plaintext at `dst` (`withSrc`): `runShort_ok`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts IsShort CopyPre condE_ok sealShort_ok powFrom_powers)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxCiph ctxH gctr inc32 ghashFrom ghash blocks ofBytes toBytes)
open VG.Proof.Gcm (lensBlock padded)

/-- The same bytes written on both sides of a frame keep it. -/
theorem frame_writeBytes_both {rs : List Region} {m₁ m₂ : Mem} (h : Frame rs m₁ m₂) (q : Addr) (xs : List Byte) :
    Frame rs (writeBytes m₁ q xs) (writeBytes m₂ q xs) := fun x hx => by
  simp only [writeBytes]
  split
  · rfl
  · exact h x hx

/-- The entry state, with `src` copied to `dst`: the state `seal` would have
entered with the plaintext at `dst`. -/
def withSrc (s₀ : State) (D S : Addr) (sl : Nat) : State :=
  { s₀ with mem := writeBytes s₀.mem D (bytesAt s₀.mem S sl) }

/-- What `seal`'s proofs need of the entry, from `seal_split`'s. -/
theorem SplitCtx.oneCtx4 {s₀ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
    (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl) :
    OneCtx (withSrc s₀ D S sl) 4 Ctx W SP Np A D nl al n :=
  ⟨C.lay, C.perm.of_eq rfl rfl, C.ww, fun i hi => C.args i (by omega),
    C.dA.sub_left (Region.sub_prefix (by omega)), C.nonce.of_eq rfl rfl, C.aad.of_eq rfl rfl,
    C.data.of_eq rfl rfl, C.rD, C.rW, C.dE, C.dAD.sub_left (Region.sub_prefix (by omega)), C.rounds, C.t_c,
    C.t_w, C.t_d, C.sp24⟩

/-- `src`, `dst` and `src_len` into `rsi`, `rdi` and `rcx`. -/
theorem copySrcArgs_ok {s₀ s : State} {Ctx W SP A D S : Addr} {n sl : Nat} (E : SEntry s₀ Ctx W SP A D S n sl s) :
    WP isa (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)),
      .mov .rcx (.mem (at_ .r15 tlenO))]) s fun s' =>
      s'.gpr .rsi = S ∧ s'.gpr .rdi = D ∧ s'.gpr .rcx = BitVec.ofNat 64 sl ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.env.r15
  have q₁ := E.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ := E.env.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := E.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have e₁ := E.src
  have e₂ := E.dat
  have e₃ := E.slen
  apply WP.of_runBlock
  refine ⟨_, by simp only [tlO, dataO, tlenO]; xrun [h15, q₁, q₂, q₃, e₁, e₂, e₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r a b c; simp [gpr_setReg, a, b, c]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

section
variable {s₀ : State} {Ctx W SP Np A D S T' : Addr} {nl al n sl : Nat}
  (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl)
include C

/-- `src`, `dst` and `src_len` into `rsi`, `rdi` and `rcx`, then `cp`, which
copies `src_len` bytes from `rsi` to `rdi`: the state `seal` would have
entered with the plaintext at `dst`, with `src` still in its slot. -/
theorem copyInto_ok {cp : Prog isa} (hsl : sl < 2 ^ 63)
    (hcp : ∀ t, CopyPre t S D sl → WP isa cp t fun t' => t'.mem = writeBytes t.mem D (bytesAt t.mem S sl) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    {s : State} (E : SEntry s₀ Ctx W SP A D S n sl s) :
    WP isa (.seq (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)),
      .mov .rcx (.mem (at_ .r15 tlenO))]) cp) s fun s' =>
      OneEntry (withSrc s₀ D S sl) Ctx W SP A D n s' ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = S := by
  have L := C.lay
  have hsl' := C.sl_le
  have dW := C.dE
  have sW := C.sW
  have hwD := C.data.ok.wrap
  -- `D`'s first `sl` bytes, apart from `W`, the context, the nonce and the data.
  have dWs : ∀ d k, d + k ≤ 2560 → (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨D, sl⟩ := fun d k h =>
    ((dW.sub_left (Region.sub_prefix hsl')).sub_right (Lay.wSub h)).symm
  refine WP.seq (WP.mono (copySrcArgs_ok E) fun s₃ ⟨si, di, cx, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have cp : CopyPre s₃ S D sl := by
    refine ⟨si, di, cx, hsl, ?_, ?_, (C.sD.sub_right (Region.sub_prefix hsl'))⟩
    · rw [rd₃, wr₃, E.rd, E.wr]; exact C.src
    · rw [wr₃, E.wr]
      exact Covers.trans (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨D, n⟩, List.mem_singleton_self _, 0, by simp, show 0 + sl ≤ n by omega⟩) C.data.wr
  refine WP.mono (hcp s₃ cp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  -- The copy writes only `D`'s first `sl` bytes, the bytes of `src` as at the entry.
  have hS : bytesAt s₃.mem S sl = bytesAt s₀.mem S sl := by
    rw [m₃]
    exact bytesAt_frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sW.sub_right (Lay.wSub (by decide))) (by have := C.sWrap; omega)
  rw [hS, m₃] at m₄
  have fD : Frame [⟨D, sl⟩] s.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have kW : ∀ d, d + 8 ≤ 2560 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => fD.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWs d 8 hd) (by decide)
  have gg : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₄.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [g₄ r d e f, g₃ r a b c]
  exact ⟨⟨E.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)) (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]),
      ⟨by rw [kW 176 (by decide)]; exact E.rounds.1, E.rounds.2⟩,
      by rw [kW 232 (by decide)]; exact E.aad, by rw [kW 184 (by decide)]; exact E.alen,
      by rw [kW 200 (by decide)]; exact E.dat, by rw [kW 208 (by decide)]; exact E.len,
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact E.r12,
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact E.rbp,
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact E.rsp,
      E.saved.frame fD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWs 128 48 (by decide)),
      by rw [m₄]; exact frame_writeBytes_both E.frame D _,
      by rw [rd₄, rd₃]; exact E.rd, by rw [wr₄, wr₃]; exact E.wr⟩,
    by rw [kW 224 (by decide)]; exact E.src⟩

/-- `src` copied to `dst`: the state `seal` enters `sealShort` with, for the
plaintext at `dst`. -/
theorem copySrc_ok {s : State} (E : SEntry s₀ Ctx W SP A D S n sl s) (hn5 : n < 512) :
    WP isa SealSplit.copySrc s (OneEntry (withSrc s₀ D S sl) Ctx W SP A D n) :=
  WP.mono (copyInto_ok C (by have := C.sl_le; omega) (fun _ h => Gather.copy_ok h) E) fun _ h => h.1

/-- The short path, after `cond`: `src` copied to `dst`, and the text sealed
there. -/
theorem shortPath_ok (hF : ShortFacts) {s : State} (E : SEntry s₀ Ctx W SP A D S n sl s)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hs : IsShort nl al n) :
    WP isa (.seq SealSplit.copySrc Short.sealShort) s (SplitRunPost s₀ Ctx W SP Np A D S nl al n sl) := by
  obtain ⟨h12, hal5, hn5, h32, -⟩ := hs
  have hsl := C.sl_le
  have hn := C.data.ok.lt
  refine WP.seq (WP.mono (copySrc_ok C E hn5) fun s₄ E' => ?_)
  refine WP.mono (sealShort_ok hF C.oneCtx4 (powFrom_powers hF) E' hNp hnl hal h12 hal5 hn5 h32) fun s₅ P => ?_
  obtain ⟨he₅, rd₅, wr₅, sv₅, f₅, hC₅, hT₅⟩ := P
  -- What `withSrc` changes: `D`'s first `sl` bytes.
  have f₀ : Frame [⟨D, sl⟩] s₀.mem (withSrc s₀ D S sl).mem := writeBytes_frame' _ (length_bytesAt _ _ _)
  have one : ∀ {Y : Region}, Y.Disjoint ⟨D, n⟩ → ∀ r ∈ [(⟨D, sl⟩ : Region)], Y.Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Region.sub_prefix hsl)
  have hR := C.rounds
  have eC : ctxCiph (withSrc s₀ D S sl).mem Ctx ((withSrc s₀ D S sl).gpr .rsi).toNat =
      ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat :=
    ciph_frame f₀ (one C.data.ctx) hR
  have eH : ctxH (withSrc s₀ D S sl).mem Ctx = ctxH s₀.mem Ctx :=
    blockAt_frame f₀ (one (C.data.ctx.sub_left (Offset.sub_base _ (by decide))))
  have eN : bytesAt (withSrc s₀ D S sl).mem Np nl = bytesAt s₀.mem Np nl :=
    bytesAt_frame f₀ (one C.nD) (by have := C.nonce.lt; omega)
  have eA : bytesAt (withSrc s₀ D S sl).mem A al = bytesAt s₀.mem A al :=
    bytesAt_frame f₀ (one C.aD) (by have := C.aad.lt; omega)
  have eP : bytesAt (withSrc s₀ D S sl).mem D n = bytesAt s₀.mem S sl ++ (bytesAt s₀.mem D n).drop sl := by
    show bytesAt (writeBytes s₀.mem D (bytesAt s₀.mem S sl)) D n = _
    rw [bytesAt_writeBytes_prefix _ _ _ (by rw [length_bytesAt]; omega) hn, length_bytesAt,
      show n = sl + (n - sl) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
      Nat.add_sub_cancel_left]
  rw [eC, eH, eN, eP] at hC₅
  rw [eC, eH, eN, eA] at hT₅
  refine ⟨he₅, rd₅, wr₅, sv₅, ?_, hC₅, hT₅⟩
  refine (f₀.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, n⟩, by simp, Region.sub_prefix hsl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 56, by simp, below_sub (by decide) (by decide)⟩

end

/-- After the entry, `seal_split` with the short path. -/
theorem runShort_ok (hF : ShortFacts) (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfin : FinOk M fin) : MidOk M (SealSplit.runShort (v.withBlk B) T.fn fin) := by
  intro s₀ s₁ Ctx W SP Np A D S T' nl al n sl C X kM E hNp hnl hal
  unfold SealSplit.runShort
  refine WP.seq (WP.mono (condE_ok C.toOneCtx E.toOneEntry hnl hal) fun s₂ ⟨hz, E₂, K⟩ => ?_)
  have S₂ : SEntry s₀ Ctx W SP A D S n sl s₂ := ⟨E₂, by rw [K.mem]; exact E.src, by rw [K.mem]; exact E.slen⟩
  refine WP.ite (decide ¬IsShort nl al n) (eval_e hz) (fun _ => splitRun_ok v B T hfin C X kM S₂ hNp hnl hal)
    fun h => ?_
  exact shortPath_ok C hF S₂ hNp hnl hal (Decidable.not_not.mp (of_decide_eq_false h))

end VG.Proof.AesGcm.X86_64.Split
