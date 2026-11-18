module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchSplit
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-! ### `AesGcm.X86_64.Split.ShortCT`, which only this module used -/

section

/-! ### `AesGcm.X86_64.Split.ShortRun`, which this module and modules that import it used -/

section

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
  ⟨C.lay, C.perm.of_eq rfl rfl, C.ww, fun i hi => C.args i (by omega_using [hi]),
    C.dA.sub_left (Region.sub_prefix (by omega_using [])), C.nonce.of_eq rfl rfl, C.aad.of_eq rfl rfl,
    C.data.of_eq rfl rfl, C.rD, C.rW, C.dE, C.dAD.sub_left (Region.sub_prefix (by omega_using [])), C.rounds, C.t_c,
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
        exact ⟨⟨D, n⟩, List.mem_singleton_self _, 0, by simp, show 0 + sl ≤ n by omega_using [hsl']⟩) C.data.wr
  refine WP.mono (hcp s₃ cp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  -- The copy writes only `D`'s first `sl` bytes, the bytes of `src` as at the entry.
  have hS : bytesAt s₃.mem S sl = bytesAt s₀.mem S sl := by
    rw [m₃]
    exact bytesAt_frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sW.sub_right (Lay.wSub (by decide))) (by have := C.sWrap; omega_using [hsl])
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
  WP.mono (copyInto_ok C (by have := C.sl_le; omega_using [hn5, this]) (fun _ h => Gather.copy_ok h) E) fun _ h => h.1

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
    bytesAt_frame f₀ (one C.nD) (by have := C.nonce.lt; omega_using [hnl])
  have eA : bytesAt (withSrc s₀ D S sl).mem A al = bytesAt s₀.mem A al :=
    bytesAt_frame f₀ (one C.aD) (by have := C.aad.lt; omega_using [hal])
  have eP : bytesAt (withSrc s₀ D S sl).mem D n = bytesAt s₀.mem S sl ++ (bytesAt s₀.mem D n).drop sl := by
    show bytesAt (writeBytes s₀.mem D (bytesAt s₀.mem S sl)) D n = _
    rw [bytesAt_writeBytes_prefix _ _ _ (by rw [length_bytesAt]; omega_using [hsl]) hn, length_bytesAt,
      show n = sl + (n - sl) by omega_using [hsl], bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
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

end

end

/-!
# AES-GCM `seal_split` on x86-64 with AVX-512: the short path, in two runs

Untrusted: everything here is checked by Lean. Two runs test the same
public lengths (`Short.cond_rel`), so take the same path: `run` (`splitRun_rel`),
or `src` copied to `dst` from the same public pointers and length
(`copySrc`, checked by the taint analysis once they are loaded) and the text
sealed there (`Short.sealShort_rel`, from the states `withSrc` describes):
`runShort_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts IsShort condE_ok condS_of cond_rel rel_next rel_piece keepsEnv
  sealShort_rel powers_ct powFrom_powers)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)

theorem copySrcArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp])
    (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
    hc).isSome = true := ⟨_, by simp only [tlO, dataO, tlenO]; taint_decide⟩

theorem gatherCopy_check : ∃ hc, (taint.check (Taint.ofRegs (([.rsi, .rdi, .rcx] : List Reg) ++
    ([.r13, .r14, .r15, .rsp] : List Reg))) SealGather.copy hc).isSome = true := ⟨_, by taint_decide⟩

/-- After the entry, `seal_split` with the short path, in two runs. -/
theorem runShort_rel (hF : ShortFacts) (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M) {fin : Prog isa}
    (hfr : FinRel M fin) : MidRel M (SealSplit.runShort (v.withBlk B) T.fn fin) := by
  intro s₀ s₀' Ctx W SP Np A D S T' nl al n sl R C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold SealSplit.runShort
  have hw : ∀ {s₀ : State} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, SEntry s₀ Ctx W SP A D S n sl s →
      WP isa Short.cond s fun u => u.zf = some (decide ¬IsShort nl al n) ∧ SEntry s₀ Ctx W SP A D S n sl u :=
    fun C hnl hal s h => WP.mono (condE_ok C.toOneCtx h.toOneEntry hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.mem]; exact h.src, by rw [K.mem]; exact h.slen⟩
  have c := rel_next (cond_rel (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (fun _ h => condS_of h.toOneEntry hnl hal) (fun _ h => condS_of h.toOneEntry hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega_using [hlt]))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((splitRun_rel v B T hfr C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsShort nl al n
  · have hn5 : n < 512 := hs.2.2.1
    have cp := rel_piece (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (b := [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
      (c := SealGather.copy)
      (G₁ := fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl)
      (G₂ := fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl)
      [.rsi, .rdi, .rcx] (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel))
      copySrcArgs_check (fun _ h => WP.mono (copySrcArgs_ok h) fun _ g => ⟨g.1, g.2.1, g.2.2.1⟩)
      (fun _ h => WP.mono (copySrcArgs_ok h) fun _ g => ⟨g.1, g.2.1, g.2.2.1⟩) (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) gatherCopy_check
    have cp' := rel_next cp (fun _ h => copySrc_ok C h hn5) (fun _ h => copySrc_ok C' h hn5)
    exact (RelCT.seq cp' ((sealShort_rel (powers_ct hF) C.oneCtx4 C'.oneCtx4 (powFrom_powers hF) (powFrom_powers hF) hNp hnl hal hR hNp' hnl' hal' hR' hs).mono
      (fun _ _ h => h) fun _ _ h => h)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.Split

end

end

/-! ### `AesGcm.X86_64.Split.End`, which only this module used -/

section

/-!
# AES-GCM `seal_split` on x86-64: the end of each instance

Untrusted: everything here is checked by Lean. `seal_split` ends as its
instance's `seal` does (`GcmImpl.splitFin`): with the keystream in `zmm5`
for the instances with the short path (`Short.finish`), in `xmm` registers
for those ending without calls (`Short.finishWith Short.finKsA`), and
otherwise with `oneCrypt` and `oneTag 0` (`SealSplit.finCalls`); and what
correctness (`splitFin_ok`), constant time (`splitFin_rel`) and the static
facts need of it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts finKs_ksOk finKs_rel finKsA_ksOk finKsA_rel)

/-- The end of `seal_split` of the implementations `v`, as their `seal`'s. -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitFin (v : GcmImpl) : Prog isa :=
  if v.short then Short.finish else if v.fin then Short.finishWith Short.finKsA else SealSplit.finCalls v.callees

variable (v : GcmImpl)

theorem splitFin_ok (hF : ShortFacts) {M : CtxMode} : FinOk M v.splitFin := by
  unfold GcmImpl.splitFin; split
  · exact finOk_finishWith hF finKs_ksOk
  · split
    · exact finOk_finishWith hF finKsA_ksOk
    · exact finCalls_ok v

theorem splitFin_rel (hF : ShortFacts) {M : CtxMode} : FinRel M v.splitFin := by
  unfold GcmImpl.splitFin; split
  · exact finRel_finishWith hF finKs_ksOk finKs_rel
  · split
    · exact finRel_finishWith hF finKsA_ksOk finKsA_rel
    · exact finRel_calls v

theorem finCalls_mx : (SealSplit.finCalls v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo,
    Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true,
    ↓reduceIte, Bool.false_eq_true]
  decide +kernel

theorem finCalls_spSafe : (SealSplit.finCalls v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo,
    Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true,
    ↓reduceIte, Bool.false_eq_true]
  decide +kernel

theorem finCalls_xdepth : (SealSplit.finCalls v.callees).x86_64Depth ≤ 24 := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv,
    Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using []

theorem finish_mx : (Short.finish : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem finish_spSafe : (Short.finish : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by decide +kernel
theorem finish_xdepth : (Short.finish : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem finishA_mx : (Short.finishWith Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem finishA_spSafe : (Short.finishWith Short.finKsA : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem splitFin_mx : v.splitFin.allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitFin; split
  · exact finish_mx
  · split
    · exact finishA_mx
    · exact finCalls_mx v

theorem splitFin_spSafe : v.splitFin.all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitFin; split
  · exact finish_spSafe
  · split
    · exact finishA_spSafe
    · exact finCalls_spSafe v

theorem splitFin_xdepth : v.splitFin.x86_64Depth ≤ 24 := by
  unfold GcmImpl.splitFin; split
  · rw [finish_xdepth]; decide
  · split
    · rw [SealFin.finishA_xdepth]; decide
    · exact finCalls_xdepth v

end VG.Proof.AesGcm.X86_64.Split

end

end


/-!
# AES-GCM `seal_split` on x86-64: `Verified`

Untrusted: everything here is checked by Lean. `seal_split` calling any
`vg_aes_gcm_encrypt_blocks_to` `T` (`BlkToFn`) loads no `mxcsr`, writes
`rsp` only in its frames and uses 56 bytes of stack (the call's arguments,
its return address and its stack), so it preserves what the ABI says; it
meets the shared contracts with a `work` buffer appended
(`sealSplitScratchContract`, …), and the shared contracts of
`Spec/Gcm/OutOfPlace.lean` and `Spec/Gcm/Prepared.lean` in a frame of 2616
bytes holding the working space (`Verified.stackArgScratch`): its 2560
bytes, a copy of the five other stack arguments, and 16 more, for 2672 bytes
of stack in all; for the key contexts of `vg_aes_gcm_init`,
`vg_aes_gcm_init_precomputed` and `vg_aes_gcm_prepare`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

/-- `seal_split`'s code after the entry for the implementations `v`: with
`seal`'s short path if they have it. -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitMid (v : GcmImpl) (c : Callees) (fTo : Fn) : Prog isa :=
  if v.short then SealSplit.runShort c fTo v.splitFin else SealSplit.run c fTo v.splitFin

theorem cond_mx : (Short.cond : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem cond_spSafe : (Short.cond : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by decide +kernel
theorem cond_xdepth : (Short.cond : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem copySrc_mx : (SealSplit.copySrc : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem copySrc_spSafe : (SealSplit.copySrc : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem copySrc_xdepth : (SealSplit.copySrc : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem sealShort_mx : (Short.sealShort : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem sealShort_spSafe : (Short.sealShort : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem sealShort_xdepth : (Short.sealShort : Prog isa).x86_64Depth = 0 := by decide +kernel

section
variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M)

theorem run_mx :
    (SealSplit.run (v.withBlk B) T.fn v.splitFin).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  have f := splitFin_mx v
  simp only [e, d, f, T.mx, SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem run_spSafe :
    (SealSplit.run (v.withBlk B) T.fn v.splitFin).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  have f := splitFin_spSafe v
  simp only [e, d, f, T.spAll, SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem run_xdepth : (SealSplit.run (v.withBlk B) T.fn v.splitFin).x86_64Depth ≤ 56 := by
  have e := B.encXd
  have d := B.decXd
  have t := T.xd
  have f := splitFin_xdepth v
  simp only [SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp,
    tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack,
    v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e, t, f]

theorem splitMid_mx : (v.splitMid (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitMid; split
  · simp only [SealSplit.runShort, Code.allInstrs]
    rw [cond_mx, run_mx v B T, copySrc_mx, sealShort_mx]; rfl
  · exact run_mx v B T

theorem splitMid_spSafe : (v.splitMid (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitMid; split
  · simp only [SealSplit.runShort, Code.all]
    rw [cond_spSafe, run_spSafe v B T, copySrc_spSafe, sealShort_spSafe]; rfl
  · exact run_spSafe v B T

theorem splitMid_xdepth : (v.splitMid (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitMid; split
  · have := run_xdepth v B T
    simp only [SealSplit.runShort, Code.x86_64Depth, cond_xdepth, copySrc_xdepth, sealShort_xdepth, Nat.max_le]
    omega_using [this]
  · exact run_xdepth v B T

theorem splitMid_ok (hF : ShortFacts) : MidOk M (v.splitMid (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMid; split
  · exact runShort_ok hF v B T (splitFin_ok v hF)
  · exact splitRun_ok v B T (splitFin_ok v hF)

theorem splitMid_rel (hF : ShortFacts) : MidRel M (v.splitMid (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMid; split
  · exact runShort_rel hF v B T (splitFin_rel v hF)
  · exact splitRun_rel v B T (splitFin_rel v hF)

theorem sealSplit_mx :
    (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.«seal», Code.allInstrs]
  rw [splitMid_mx v B T]; rfl

theorem sealSplit_spSafe :
    (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.«seal», Code.all]
  rw [splitMid_spSafe v B T]; rfl

theorem sealSplit_xdepth : (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).x86_64Depth ≤ 56 := by
  have := splitMid_xdepth v B T
  simp only [SealSplit.«seal», Code.x86_64Depth, tagOut, Nat.max_le]
  omega_using [this]

theorem sealSplit_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealSplitX86_64M M).pre s) :
    ∃ t s', Exec isa (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealSplitM_wp (splitMid_ok v B T hF) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealSplit_mx v B T) he hg, hp⟩

end

/-! ## The contracts -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_split` with its
working space (with no data and empty `src`, and `dst` and `work` at 0). -/
def splitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8029 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 48⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

/-- `splitSat`, with a key context of 1024 bytes. -/
def splitSatP : State := { splitSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 48⟩] }

theorem split_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.base).Implies
    (Proof.AesGcm.sealSplitScratchContract X86_64.abi 56) := by
  sig_implies [Proof.AesGcm.sealSplitScratchContract, Proof.AesGcm.sealSplitScratchSig, Proof.Gcm.sealSplitPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.base] [splitSat] using splitSat

theorem splitP_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.powers).Implies
    (Proof.AesGcm.sealSplitPrecomputedScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig,
              Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine powersRepr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem splitPrepared_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared).Implies
    (Proof.AesGcm.sealSplitPreparedScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig,
              Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre, X86_64.abi,
              X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine preparedPowersRepr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

section
variable (v : GcmImpl) (hF : ShortFacts)
include hF

theorem sealSplit_core (B : BlkFn CtxMode.base) (T : BlkToFn CtxMode.base) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)) (Proof.AesGcm.sealSplitScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.base) (sealSplit_correct v B T hF)
    (sealSplitM_ct (splitMid_ok v B T hF) (splitMid_rel v B T hF)) split_implies

theorem sealSplitP_core (B : BlkFn CtxMode.powers) (T : BlkToFn CtxMode.powers) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPrecomputedScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.powers) (sealSplit_correct v B T hF)
    (sealSplitM_ct (splitMid_ok v B T hF) (splitMid_rel v B T hF)) splitP_implies

end

/-! ## In its frame -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_split`, without
the working space. -/
def splitFrameSat : State :=
  { splitSat with
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

/-- `splitFrameSat`, with a key context of 1024 bytes. -/
def splitFrameSatP : State :=
  { splitFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩] }

theorem splitFrameSat_pre : ∃ s, (Proof.Gcm.sealSplitContract X86_64.abi 2672).pre s := by
  implies_sat [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, Proof.Gcm.sealSplitPost,
    X86_64.abi, X86_64.argRegs] [splitFrameSat, splitSat] using splitFrameSat

theorem splitFrameSatP_pre : ∃ s, (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, Proof.Gcm.sealSplitPrecomputedPre,
    Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP, splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine powersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem splitFrameSatPrepared_pre : ∃ s, (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPreparedPre, Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP,
    splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

section
variable (v : GcmImpl) (hF : ShortFacts)
include hF

theorem sealSplit_framed (B : BlkFn CtxMode.base) (T : BlkToFn CtxMode.base) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.sealSplitPostOut_local _) (sig := Proof.Gcm.sealSplitSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplit_core v hF B T) (by decide) (by decide) (by decide)
    (sealSplit_spSafe v B T) (sealSplit_xdepth v B T) (Proof.AesGcm.sealSplitPre_local _)
    (Proof.AesGcm.sealSplitPost_local _) splitFrameSat_pre

theorem sealSplitP_framed (B : BlkFn CtxMode.powers) (T : BlkToFn CtxMode.powers) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.sealSplitPrecomputedPostOut_local _) (sig := Proof.Gcm.sealSplitPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitP_core v hF B T) (by decide) (by decide) (by decide)
    (sealSplit_spSafe v B T) (sealSplit_xdepth v B T) (Proof.AesGcm.sealSplitPrecomputedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatP_pre

end

end VG.Proof.AesGcm.X86_64.Split
