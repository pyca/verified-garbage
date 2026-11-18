module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.EntryBranch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-! ### `ChaCha20Poly1305.X86_64.CallOpen`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on x86-64: the call of `open`'s body

`open` and `open_to` call the same functions, `vg_chacha20_poly1305_open_body*`
(`Shared.callOpen`), whose code (`Shared.openInner`: `openShared`, or the
stitched `openStitchedShared`) is verified once, against `sharedK`
(`OpenTail.lean`): from `open`'s entry state with the ciphertext's address
in `r11`. Each caller loads `work` into `rax`, `tag` into `r10`, the
destination's address into `r8` and the ciphertext's into `r11`, and then
pushes `r11` (padding), `work` and `tag`, which, with the call's return
address below them, lay out `open`'s entry for the callee.

`callOpen_ok` and `callOpen_rel` state what the call does from such a state
(`CPre`: the regions the callee reads and writes, apart from each other as
`open`'s contract has them and from the 56 bytes of stack the frame and the
callee use), through what it reads of that state, so that each caller's
proof only lays out its entry (`Shared.lean`, `OpenTo.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.CallOpen

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.ChaCha20.X86_64 (XorImpl)

/-! ## The callee -/

/-- The code of the callee, for the implementation `v` of `vg_chacha20_xor`. -/
abbrev inner (v : XorImpl) : Prog isa := openInner v.callee v.poly

/-- The padding before the stitched code: `rax` zeroed. -/
theorem pad_ok (s : State) : WP isa (.block (Stitch.padIns .rax 41)) s fun u => u = s.setReg .rax 0 := by
  rw [show Stitch.padIns .rax 41 = [.mov32 .rax (.imm 0), .mov32 .rax (.imm 0), .mov32 .rax (.imm 0),
    .mov32 .rax (.imm 0), .mov32 .rax (.imm 0), .mov32 .rax (.imm 0), .mov32 .rax (.imm 0),
    .mov .rax (.reg .rax), .mov .rax (.reg .rax)] from rfl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, setReg_setReg]
  rw [show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) by decide]

/-- `APre` does not depend on `rax`. -/
theorem apre_setRax {s : State} (hp : APre false s) (v : BitVec 64) : APre false (s.setReg .rax v) := by
  obtain ⟨⟨more, h1⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := hp
  exact ⟨⟨more, h1⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩

/-- Nor does `sharedK`'s precondition. -/
theorem spre_setRax {s : State} (hp : SPreO s) (v : BitVec 64) : SPreO (s.setReg .rax v) := by
  obtain ⟨ha, ⟨lt, wrap, ctx, stk, cov⟩, d⟩ := hp
  exact ⟨apre_setRax ha v, ⟨lt, wrap, ctx, stk, cov⟩, d⟩

theorem inner_ok (v : XorImpl) (s : State) (hs : sharedK.pre s) :
    ∃ t s', Exec isa (inner v) s t s' ∧ abiPreserved s s' ∧ sharedK.post s s' := by
  by_cases hv : v.poly = .avx2
  · have hw : WP isa (.seq (.block (Stitch.padIns .rax 41)) (Stitch.openStitchedShared v.callee v.poly)) s
        fun s' => abiPreserved s s' ∧ sharedK.post s s' := by
      refine WP.seq (WP.mono (pad_ok s) fun u e => ?_)
      subst e
      obtain ⟨t, s', ex, ab, hq⟩ := Stitch.stitchedShared_ok v hv _ (spre_setRax hs 0)
      refine ⟨t, s', ex, ⟨fun r hr => ?_, ?_, ab.2.2⟩, hq⟩
      · have hne : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
        rw [ab.1 r hr, RegUpd.gpr_setReg_of_ne _ _ hne]
      · have := ab.2.1
        rwa [RegUpd.gpr_setReg_of_ne _ _ (by decide)] at this
    rw [hv] at hw
    obtain ⟨t, s', ex, hq⟩ := hw
    exact ⟨t, s', by simpa only [inner, openInner, hv, ↓reduceIte] using ex, hq⟩
  · simpa only [inner, openInner, hv, ↓reduceIte] using shared_ok v s hs

theorem inner_ct (v : XorImpl) : ConstantTime isa sharedK.pre sharedK.pub (inner v) := by
  by_cases hv : v.poly = .avx2
  · have hpad : ∃ hc, (taint.check (Taint.ofRegs []) (.block (Stitch.padIns .rax 41)) hc).isSome = true :=
      ⟨_, by taint_decide⟩
    have h : ConstantTime isa sharedK.pre sharedK.pub
        (.seq (.block (Stitch.padIns .rax 41)) (Stitch.openStitchedShared v.callee v.poly)) :=
      Gather.ct_of fun σ₁ σ₂ p₁ p₂ hq =>
        Gather.rel_seq (Gather.rel_regs [] (by simp) hpad) (pad_ok σ₁) (pad_ok σ₂)
          fun τ₁ τ₂ e₁ e₂ => by
            subst e₁ e₂
            exact Stitch.stitchedShared_rel v hv (spre_setRax p₁ 0) (spre_setRax p₂ 0) hq
    rw [hv] at h
    simpa only [inner, openInner, hv, ↓reduceIte] using h
  · simpa only [inner, openInner, hv, ↓reduceIte] using shared_ct v

theorem inner_avx2 (v : XorImpl) (hv : v.poly = .avx2) :
    inner v = .seq (.block (Stitch.padIns .rax 41)) (Stitch.openStitchedShared v.callee .avx2) := by
  simp only [inner, openInner, hv, ↓reduceIte]

theorem inner_shared (v : XorImpl) (hv : ¬v.poly = .avx2) : inner v = openShared v.callee v.poly := by
  simp only [inner, openInner, hv, ↓reduceIte]

/-- `sharedK`, with what the code leaves in the keystream area (`KsLeftZ`) in
its postcondition. -/
def sharedKL (v : XorImpl) : Contract isa where
  pre := SPreO
  post s s' := openSPost s s' ∧ KsLeftZ v (cx s) (L s) s.mem s'.mem
  pub := sharedPub

/-- The shared code leaves the keystream area as `KsLeftZ` says
(`shared_correctK`, `Stitch.stitchedShared_correctK`). -/
theorem inner_okL (v : XorImpl) (s : State) (hs : (sharedKL v).pre s) :
    ∃ t s', Exec isa (inner v) s t s' ∧ abiPreserved s s' ∧ (sharedKL v).post s s' := by
  by_cases hv : v.poly = .avx2
  · have hw : WP isa (.seq (.block (Stitch.padIns .rax 41)) (Stitch.openStitchedShared v.callee v.poly)) s
        fun s' => abiPreserved s s' ∧ (sharedKL v).post s s' := by
      refine WP.seq (WP.mono (pad_ok s) fun u e => ?_)
      subst e
      obtain ⟨t, s', ex, ⟨ab, hq⟩, k⟩ := Stitch.stitchedShared_correctK v hv (spre_setRax hs 0)
      have em : (s.setReg .rax 0).mem = s.mem := RegUpd.mem_setReg _ _ _
      have ec : cx (s.setReg .rax 0) = cx s := by
        simp only [cx, X86_64.stackArg, X86_64.stackArgAddr, RegUpd.gpr_setReg_of_ne _ _ (show Reg.rsp ≠ .rax by decide), em]
      have eL : L (s.setReg .rax 0) = L s := by
        simp only [L, RegUpd.gpr_setReg_of_ne _ _ (show Reg.r9 ≠ .rax by decide)]
      rw [ec, eL, em] at k
      refine ⟨t, s', ex, ⟨fun r hr => ?_, ?_, ab.2.2⟩, hq, k⟩
      · have hne : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
        rw [ab.1 r hr, RegUpd.gpr_setReg_of_ne _ _ hne]
      · have := ab.2.1
        rwa [RegUpd.gpr_setReg_of_ne _ _ (by decide)] at this
    rw [inner_avx2 v hv]
    rw [hv] at hw
    exact hw
  · rw [inner_shared v hv]
    obtain ⟨t, s', e, ⟨a, p⟩, k⟩ := shared_correctK v hs
    exact ⟨t, s', e, a, p, KsLeftAt.z hv k⟩

open VG.Impl.ChaCha20Poly1305.X86_64.Stitch VG.Proof.ChaCha20Poly1305.X86_64.Stitch in
/-- The callee never writes the stack pointer. The callees' code is
generalized away (`P`), so that `simp` does not unfold the predicate, and the
kernel checks the rest once for each configuration of `fold`, `pass` and
`wide`. -/
theorem inner_spSafe (v : XorImpl) : (inner v).all (fun i => !isa.writesSp i) = true := by
  by_cases hv : v.poly = .avx2
  · rw [inner_avx2 v hv]
    obtain ⟨hf, hpass, hw⟩ := avx2_of v hv
    have hc := v.spSafe
    have ho := bulkO_spSafe v.callee.vl
    have hk := twoKs_spSafe v.callee.vl
    have hk4 := fourKs_spSafe v.callee.vl
    have hwo := wholeO_spSafe v.callee.vl
    have hkB := twoKsB_spSafe v.callee.vl
    have hb := blocks_spSafe .avx2
    generalize hP : (fun i => !isa.writesSp i) = P at hc hb ho hk hk4 hwo hkB ⊢
    rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;> rw [hl] at ho hk hk4 hwo hkB <;>
    simp only [Impl.ChaCha20.X86_64.Callee.inPlace, dataCopy, openStitchedShared, openStitchedBody, openTail,
      zeroData, prologueX, xsel, xselV, xselA, hl, ↓reduceIte, Bool.false_eq_true, cryptO, decRest, xorTail,
      xorKs, callX, Bool.cond_true, Impl.ChaCha20.X86_64.Xor.callTo, Code.all, hc, hb, ho, hk, hk4, hkB, hwo,
      hf, hpass, hw, macPad, macPadLengths, Code.iteCold, wholeBlocks, padRest, Bool.cond_false, padCopy,
      padTail, absorbLengths, Bool.and_true, Bool.true_and] <;>
    subst hP <;> lit_decide
  · rw [inner_shared v hv]
    have hc := v.spSafe
    have hb := blocks_spSafe v.poly
    generalize hP : (fun i => !isa.writesSp i) = P at hc hb ⊢
    rcases v.fold_poly with ⟨hf, hpass, hw, hpo⟩ | ⟨hf, hpass, hw, hpo⟩ | ⟨hf, hpass, hw, hpo | hpo⟩
    · rw [hpo] at hb ⊢
      simp only [Impl.ChaCha20.X86_64.Callee.inPlace, dataCopy, openShared, openBody, openTail, zeroData,
        prologue, crypt, cryptBig, xorKs, callX, Code.all, hc, hb, hf, hpass, hw, macPad, macPadLengths,
        Code.iteCold, wholeBlocks, padRest, Bool.cond_true, Bool.cond_false, padCopy, padTail, absorbLengths,
        Bool.and_true, Bool.true_and]
      subst hP; lit_decide
    · exact absurd hpo hv
    all_goals
      rw [hpo] at hb ⊢
      simp only [Impl.ChaCha20.X86_64.Callee.inPlace, dataCopy, openShared, openBody, openTail, zeroData,
        prologue, crypt, cryptBig, xorKs, callX, Code.all, hc, hb, hf, hpass, hw, macPad, macPadLengths,
        Code.iteCold, wholeBlocks, padRest, Bool.cond_true, Bool.cond_false, padCopy, padTail, absorbLengths,
        Bool.and_true, Bool.true_and]
      subst hP; lit_decide

open VG.Impl.ChaCha20Poly1305.X86_64.Stitch VG.Proof.ChaCha20Poly1305.X86_64.Stitch in
theorem inner_xdepth (v : XorImpl) : (inner v).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  have hc := padRest_xdepth (dataCopy v.poly) v.poly 2
  have ha := padSite_xdepth (dataCopy v.poly) v.poly .rbx .rbp
  by_cases hv : v.poly = .avx2
  · rw [inner_avx2 v hv]
    rw [hv] at hb hc ha
    rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;>
    simp only [Impl.ChaCha20.X86_64.Callee.inPlace, openStitchedShared, openStitchedBody, openTail, zeroData,
      prologueX, xsel, xselV, xselA, hl, ↓reduceIte, Bool.false_eq_true, twoKsB_xdepth, prologueA, prologueB,
      zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks, padRest, padCopy, padTail, cryptO, decRest,
      xorTail, xorKs, callX, Bool.cond_true, Impl.ChaCha20.X86_64.Xor.callTo, absorbLengths, finalizeTo,
      finalizeWith, Code.x86_64Depth, xorBufTo_xdepth, xorTail_xdepth, foldM_xdepth, wipeL_xdepth,
      init_xdepth, finalize_xdepth, bulkO_xdepth, wholeO_xdepth, twoKs_xdepth, fourKs_xdepth,
      Nat.max_le, Nat.zero_max, Nat.max_zero, Nat.max_self, Nat.zero_le, true_and, and_true,
      and_self] at hc ha ⊢ <;>
    omega_arith
  · rw [inner_shared v hv]
    simp only [Impl.ChaCha20.X86_64.Callee.inPlace, openShared, openBody, openTail, zeroData, prologue,
      prologueA, prologueB, zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks, padRest, padCopy,
      padTail, crypt, cryptBig, cryptPre, xorKs, callX, Bool.cond_true, Impl.ChaCha20.X86_64.Xor.callTo,
      absorbLengths, finalizeTo, finalizeWith, Code.x86_64Depth, xorBufTo_xdepth, foldM_xdepth, init_xdepth,
      finalize_xdepth, Nat.max_le, Nat.zero_max, Nat.max_zero, Nat.max_self, Nat.zero_le, true_and, and_true,
      and_self] at hc ha ⊢
    omega_using [hx, hb, hc, ha]

theorem callOpen_eq (v : XorImpl) : callOpen v.callee v.poly =
    .frame (.push [.r11, .rax, .r10]) (.call (bodyName false v.callee v.poly) (inner v)) (.pop .r10 3) := rfl

theorem callOpen_spSafe (v : XorImpl) : (callOpen v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  simp only [callOpen, Code.all, inner_spSafe v, Bool.and_true]
  decide

theorem callOpen_xdepth (v : XorImpl) : (callOpen v.callee v.poly).x86_64Depth ≤ 56 := by
  have h : (openInner v.callee v.poly).x86_64Depth ≤ 24 := inner_xdepth v
  simp only [callOpen, Code.x86_64Depth, X86_64.Instr.frameBytes]
  change _ + 8 + 24 ≤ 56
  exact Nat.add_le_add_right (Nat.add_le_add_right h 8) 24

/-! ## The caller's state -/

section
variable (h : State)
/-- What the call reads of the caller's state, before the push. -/
abbrev hD : Addr := h.gpr .r8
abbrev hS : Addr := h.gpr .r11
abbrev hT : Addr := h.gpr .r10
abbrev hW : Addr := h.gpr .rax
abbrev hL : Nat := (h.gpr .r9).toNat
/-- The 56 bytes of stack below `rsp` the frame (24), the return address and
the callee (24) use. -/
abbrev hB : Addr := h.gpr .rsp - BitVec.ofNat 64 56
abbrev hkR : Region := ⟨h.gpr .rdi, 32⟩
abbrev hnR : Region := ⟨h.gpr .rsi, 12⟩
abbrev haR : Region := ⟨h.gpr .rdx, (h.gpr .rcx).toNat⟩
abbrev hsR : Region := ⟨hS h, hL h⟩
abbrev hdR : Region := ⟨hD h, hL h⟩
abbrev htR : Region := ⟨hT h, 16⟩
abbrev hwR : Region := ⟨hW h, 1696⟩
abbrev hstk : Region := ⟨hB h, 56⟩
end

/-- What the call needs of the caller's state: `open`'s precondition, with
the ciphertext at `r11` (the data, or apart from it), and 56 bytes of stack
apart from every buffer. -/
structure CPre (h : State) : Prop where
  sp_lo : 56 ≤ (h.gpr .rsp).toNat
  rd : Covers [hkR h, hnR h, haR h, htR h, hsR h] (h.rd ++ h.wr)
  wr : Covers [hdR h, hwR h] h.wr
  w_k : (hwR h).Disjoint (hkR h)
  w_n : (hwR h).Disjoint (hnR h)
  w_a : (hwR h).Disjoint (haR h)
  w_d : (hwR h).Disjoint (hdR h)
  w_t : (hwR h).Disjoint (htR h)
  d_k : (hdR h).Disjoint (hkR h)
  d_n : (hdR h).Disjoint (hnR h)
  d_a : (hdR h).Disjoint (haR h)
  d_t : (hdR h).Disjoint (htR h)
  s_w : (hsR h).Disjoint (hwR h)
  s_d : hS h = hD h ∨ (hdR h).Disjoint (hsR h)
  b_k : (hstk h).Disjoint (hkR h)
  b_n : (hstk h).Disjoint (hnR h)
  b_a : (hstk h).Disjoint (haR h)
  b_s : (hstk h).Disjoint (hsR h)
  b_d : (hstk h).Disjoint (hdR h)
  b_t : (hstk h).Disjoint (htR h)
  b_w : (hstk h).Disjoint (hwR h)
  o_k : (h.gpr .rdi).toNat + 32 ≤ 2 ^ 64
  o_n : (h.gpr .rsi).toNat + 12 ≤ 2 ^ 64
  o_a : (h.gpr .rdx).toNat + (h.gpr .rcx).toNat ≤ 2 ^ 64
  o_s : (hS h).toNat + hL h ≤ 2 ^ 64
  o_d : (hD h).toNat + hL h ≤ 2 ^ 64
  o_t : (hT h).toNat + 16 ≤ 2 ^ 64
  o_w : (hW h).toNat + 1696 ≤ 2 ^ 64

/-- What `open` decrypts, from the caller's state: the result, and the
plaintext at the destination, or zeros there. -/
def hPost (h z : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (bytesAt h.mem (h.gpr .rdi) 32) (bytesAt h.mem (h.gpr .rsi) 12)
      (bytesAt h.mem (h.gpr .rdx) (h.gpr .rcx).toNat) (bytesAt h.mem (hS h) (hL h))
      (bytesAt h.mem (hT h) 16) with
  | some pt => (z.gpr .rax).setWidth 32 = 1 ∧ bytesAt z.mem (hD h) (hL h) = pt
  | none => (z.gpr .rax).setWidth 32 = 0 ∧ bytesAt z.mem (hD h) (hL h) = List.replicate (hL h) 0

/-- What the call may leak: whether the tag is right. -/
def hLeak (h : State) : List Nat :=
  [if (Spec.ChaCha20Poly1305.decrypt (bytesAt h.mem (h.gpr .rdi) 32) (bytesAt h.mem (h.gpr .rsi) 12)
      (bytesAt h.mem (h.gpr .rdx) (h.gpr .rcx).toNat) (bytesAt h.mem (hS h) (hL h))
      (bytesAt h.mem (hT h) 16)).isSome then 1 else 0]

/-- What the call leaves: the caller's callee-saved registers, `rsp`
included, and permissions; memory changed only in the destination, `work`
and the stack the call uses; MXCSR's bits `abiPreserved` keeps; and what
`open` decrypts. -/
structure COut (h z : State) : Prop where
  cs : ∀ r ∈ calleeSaved, z.gpr r = h.gpr r
  rd : z.rd = h.rd
  wr : z.wr = h.wr
  mem : Frame [hdR h, hwR h, hstk h] h.mem z.mem
  mx : z.mxcsr.extractLsb' 6 10 = h.mxcsr.extractLsb' 6 10
  post : hPost h z

/-- What two runs of the call agree on: what it reads of the registers, and
whether the tag is right. -/
structure CPub (h₁ h₂ : State) : Prop where
  rdi : h₁.gpr .rdi = h₂.gpr .rdi
  rsi : h₁.gpr .rsi = h₂.gpr .rsi
  rdx : h₁.gpr .rdx = h₂.gpr .rdx
  rcx : h₁.gpr .rcx = h₂.gpr .rcx
  r8 : h₁.gpr .r8 = h₂.gpr .r8
  r9 : h₁.gpr .r9 = h₂.gpr .r9
  r10 : h₁.gpr .r10 = h₂.gpr .r10
  r11 : h₁.gpr .r11 = h₂.gpr .r11
  rax : h₁.gpr .rax = h₂.gpr .rax
  rsp : h₁.gpr .rsp = h₂.gpr .rsp
  leak : hLeak h₁ = hLeak h₂
  mx : h₁.mxcsr = h₂.mxcsr

/-! ## The callee's entry -/

/-- The registers the frame pushes: a word of padding, `work` and `tag`. -/
abbrev frameRegs : List Reg := [.r11, .rax, .r10]

/-- The callee's entry state. -/
abbrev eS (h : State) : State := (pushed frameRegs h).callEntry

/-- What the callee may read and write: `open`'s regions, and the
ciphertext. -/
abbrev rdB (u : State) : List Region := [kR u, nR u, aR u, tR u, argR u]
abbrev wrB (u : State) : List Region := [dR u, ctxR u]
abbrev srcR (u : State) : Region := ⟨sp u, L u⟩
/-- The callee's entry state, with those permissions. -/
abbrev nS (u : State) : State := u.withRegions (rdB u ++ [srcR u]) (wrB u)

theorem sub_hB (h : State) {a : Nat} (ha : a ≤ 56) :
    h.gpr .rsp - BitVec.ofNat 64 a = hB h + BitVec.ofNat 64 (56 - a) := Offset.sub_ofNat_eq _ ha

theorem rsp_eq (h : State) : h.gpr .rsp = hB h + BitVec.ofNat 64 56 := (BitVec.sub_add_cancel _ _).symm

/-- The callee's entry state, from the caller's. -/
structure Entry (h u : State) : Prop where
  gpr : ∀ r, r ≠ .rsp → u.gpr r = h.gpr r
  rsp : u.gpr .rsp = hB h + BitVec.ofNat 64 24
  a0 : u.mem.readW (hB h + BitVec.ofNat 64 32) 64 = hT h
  a1 : u.mem.readW (hB h + BitVec.ofNat 64 40) 64 = hW h
  mem : Frame [⟨hB h + BitVec.ofNat 64 24, 32⟩] h.mem u.mem
  rd : u.rd = h.rd
  wr : u.wr = ⟨hB h + BitVec.ofNat 64 32, 24⟩ :: h.wr
  mx : u.mxcsr = h.mxcsr

namespace CPre

variable {h : State} (hs : CPre h)
include hs

theorem hB_lt : (hB h).toNat + 56 ≤ 2 ^ 64 := by
  have := hs.sp_lo
  rw [toNat_sub_ofNat (by omega_using [this])]; omega_using []

omit hs in
/-- A part of the 56 bytes of stack is apart from a region apart from all of
them. -/
theorem stk_disj {r : Region} (hd : (hstk h).Disjoint r) {d n : Nat} (hdn : d + n ≤ 56) :
    (⟨hB h + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  hd.sub_left (Offset.sub_base _ hdn)

omit hs in
theorem stk0 {r : Region} (hd : (hstk h).Disjoint r) {n : Nat} (hn : n ≤ 56) :
    (⟨hB h, n⟩ : Region).Disjoint r :=
  hd.sub_left (Region.sub_prefix hn)

theorem entry : Entry h (eS h) := by
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega_using [this]
  have hB' := hs.hB_lt
  obtain ⟨pf, pw⟩ := pushRegs_mem h frameRegs (by decide) hn
  rw [sub_hB h (by decide)] at pf
  have pw' : ∀ j (hj : j < 3) (d : Nat), d + 8 * (j + 1) = 56 →
      (pushed frameRegs h).mem.readW (hB h + BitVec.ofNat 64 d) 64 = h.gpr frameRegs[j] := by
    intro j hj d hd
    have := pw j hj
    rw [sub_hB h (by omega_using [hj]), show 56 - 8 * (j + 1) = d by omega_using [hd]] at this
    exact this
  have prsp : (pushed frameRegs h).gpr .rsp = hB h + BitVec.ofNat 64 32 := by
    rw [pushed_rsp, sub_hB h (by decide)]; rfl
  have h32 : hB h + BitVec.ofNat 64 32 - 8 = hB h + BitVec.ofNat 64 24 := by
    rw [show (32 : Nat) = 24 + 8 from rfl, ← Offset.add_ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  have ersp : (eS h).gpr .rsp = hB h + BitVec.ofNat 64 24 := by
    rw [State.callEntry_rsp, prsp, h32]
  -- The return address, below the pushed words.
  have fr : Frame [⟨hB h + BitVec.ofNat 64 24, 8⟩] (pushed frameRegs h).mem (eS h).mem := by
    rw [State.callEntry_mem]
    refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
    rw [prsp, h32]
    exact Region.contains_self _ _
  have rw' : ∀ d, 32 ≤ d → d + 8 ≤ 56 →
      (eS h).mem.readW (hB h + BitVec.ofNat 64 d) 64 = (pushed frameRegs h).mem.readW (hB h + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fr.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by omega_using [])) (by decide)
  refine ⟨fun r hr => ?_, ersp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  · rw [rw' 32 (by decide) (by decide), pw' 2 (by decide) 32 (by decide)]; rfl
  · rw [rw' 40 (by decide) (by decide), pw' 1 (by decide) 40 (by decide)]; rfl
  · refine Frame.trans (Frame.sub pf fun r hr => ?_) (Frame.sub fr fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · rfl
  · show (pushed frameRegs h).wr = _
    rw [pushed_wr, sub_hB h (by decide)]; rfl
  · show (pushed frameRegs h).mxcsr = _
    rw [pushed_mxcsr]

end CPre

/-! ## The callee's precondition -/

theorem stackArg_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArg (s.withRegions rd wr) j = stackArg s j := rfl
theorem stackArgAddr_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArgAddr (s.withRegions rd wr) j = stackArgAddr s j := rfl

theorem sub24 (B : Addr) : B + BitVec.ofNat 64 24 - 24 = B := BitVec.add_sub_cancel _ _
theorem sub24' (B : Addr) : B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24 = B := BitVec.add_sub_cancel _ _

theorem cov_of {r : Region} {L ys : List Region} (hc : Covers L ys) (hr : r ∈ L) : Covers [r] ys :=
  Covers.trans (Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hr) hc

namespace Entry

variable {h u : State} (hb : Entry h u)
include hb

theorem addr (j : Nat) : stackArgAddr u j = hB h + BitVec.ofNat 64 (24 + 8 * (j + 1)) := by
  show u.gpr .rsp + _ = _
  rw [hb.rsp, Offset.add_ofNat_add_ofNat]

theorem arg0 : stackArg u 0 = hT h := by
  show u.mem.readW (stackArgAddr u 0) 64 = _; rw [hb.addr]; exact hb.a0
theorem arg1 : stackArg u 1 = hW h := by
  show u.mem.readW (stackArgAddr u 1) 64 = _; rw [hb.addr]; exact hb.a1

theorem rdi : u.gpr .rdi = h.gpr .rdi := hb.gpr _ (by decide)
theorem rsi : u.gpr .rsi = h.gpr .rsi := hb.gpr _ (by decide)
theorem rdx : u.gpr .rdx = h.gpr .rdx := hb.gpr _ (by decide)
theorem rcx : u.gpr .rcx = h.gpr .rcx := hb.gpr _ (by decide)
theorem r8 : u.gpr .r8 = h.gpr .r8 := hb.gpr _ (by decide)
theorem r9 : u.gpr .r9 = h.gpr .r9 := hb.gpr _ (by decide)
theorem r11 : u.gpr .r11 = h.gpr .r11 := hb.gpr _ (by decide)

theorem ek : kR u = hkR h := by show (⟨u.gpr .rdi, 32⟩ : Region) = _; rw [hb.rdi]
theorem en : nR u = hnR h := by show (⟨u.gpr .rsi, 12⟩ : Region) = _; rw [hb.rsi]
theorem ea : aR u = haR h := by
  show (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region) = _; rw [hb.rdx, hb.rcx]
theorem et : tR u = htR h := by show (⟨stackArg u 0, 16⟩ : Region) = _; rw [hb.arg0]
theorem eg : argR u = ⟨hB h + BitVec.ofNat 64 32, 16⟩ := by
  show (⟨stackArgAddr u 0, 16⟩ : Region) = _; rw [hb.addr]
theorem es : srcR u = hsR h := by
  show (⟨u.gpr .r11, (u.gpr .r9).toNat⟩ : Region) = _; rw [hb.r11, hb.r9]
theorem ed : dR u = hdR h := by
  show (⟨u.gpr .r8, (u.gpr .r9).toNat⟩ : Region) = _; rw [hb.r8, hb.r9]
theorem ec : ctxR u = hwR h := by show (⟨stackArg u 1, 1696⟩ : Region) = _; rw [hb.arg1]

variable (hs : CPre h)
include hs

/-- `open`'s precondition, narrowed. -/
theorem pre : preX86_64 false (u.withRegions (rdB u) (wrB u)) := by
  have e0 := hb.arg0
  have e1 := hb.arg1
  have eA := hb.addr 0
  simp only [preX86_64, stackArg_wr, stackArgAddr_wr, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, Bool.false_eq_true, ite_false, kR, nR, aR, argR, dR, tR, ctxR, kp, np, ad, AL, dp,
    L, tp, cx, e0, e1, eA, hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9, hb.rsp, true_and, sub24, rdB, wrB,
    Nat.reduceAdd, Nat.reduceMul]
  refine ⟨hs.w_k, hs.w_n, hs.w_a, hs.w_d, hs.w_t,
    (CPre.stk_disj hs.b_w (d := 32) (n := 16) (by decide)).symm, hs.d_k, hs.d_n, hs.d_a, hs.d_t,
    (CPre.stk_disj hs.b_d (d := 32) (n := 16) (by decide)).symm,
    CPre.stk_disj hs.b_w (d := 24) (n := 8) (by decide), CPre.stk_disj hs.b_a (d := 24) (n := 8) (by decide),
    CPre.stk_disj hs.b_d (d := 24) (n := 8) (by decide), CPre.stk_disj hs.b_t (d := 24) (n := 8) (by decide),
    CPre.stk0 hs.b_w (by decide), CPre.stk0 hs.b_k (by decide), CPre.stk0 hs.b_n (by decide),
    CPre.stk0 hs.b_a (by decide), CPre.stk0 hs.b_d (by decide), CPre.stk0 hs.b_t (by decide),
    hs.o_w, hs.o_a, hs.o_d, hs.o_t, hs.o_k, hs.o_n, by
      have := hs.sp_lo
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega⟩

/-- The callee's precondition, narrowed. -/
theorem spre : SPreO (nS u) := by
  have hp := APre.of_more (more := [srcR u]) (hb.pre hs)
  have hB' := hs.hB_lt
  refine ⟨hp, ⟨?_, ?_, ?_, ?_, Covers.of_mem fun r hr => ?_⟩, ?_⟩ <;>
    simp only [srcR, sp, L, ctxR, stkR, dR, dp, cx, stackArg_wr, State.withRegions_gpr, hb.arg1, hb.r11, hb.r9,
      hb.r8, hb.rsp, below, sub24'] at *
  · exact (h.gpr .r9).isLt
  · exact hs.o_s
  · exact hs.s_w.symm
  · exact CPre.stk0 hs.b_s (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    simp [sp, L, hb.r11, hb.r9]
  · rcases hs.s_d with e | e
    · exact .inl e
    · exact .inr e

theorem rd_cov : Covers (rdB u ++ [srcR u]) (u.rd ++ u.wr) := by
  have hc : Covers (h.rd ++ h.wr) (u.rd ++ u.wr) := Covers.of_mem fun r hr => by
    rw [hb.rd, hb.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hr := Covers.trans hs.rd hc
  show Covers [kR u, nR u, aR u, tR u, argR u, srcR u] _
  rw [hb.ek, hb.en, hb.ea, hb.et, hb.eg, hb.es]
  refine Covers.cons (cov_of hr (by simp)) (Covers.cons (cov_of hr (by simp)) (Covers.cons (cov_of hr (by simp))
    (Covers.cons (cov_of hr (by simp)) (Covers.cons ?_ (Covers.cons (cov_of hr (by simp)) Covers.nil)))))
  refine Covers.right (Covers.of_sub fun r hr' => ?_)
  simp only [List.mem_singleton] at hr'; subst hr'
  exact ⟨⟨hB h + BitVec.ofNat 64 32, 24⟩, by rw [hb.wr]; exact List.mem_cons_self .., 0,
    (BitVec.add_zero _).symm, by show 0 + 16 ≤ 24; decide⟩

theorem wr_cov : Covers (wrB u) u.wr := by
  show Covers [dR u, ctxR u] _
  rw [hb.ed, hb.ec]
  exact Covers.trans hs.wr (Covers.of_mem fun r hr => by rw [hb.wr]; exact List.mem_cons_of_mem _ hr)

omit hs in
/-- The memory of the callee's entry state, apart from the stack. -/
theorem bytes_eq {p : Addr} {n : Nat} (hk : (hstk h).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt u.mem p n = bytesAt h.mem p n :=
  bytesAt_frame hb.mem (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (CPre.stk_disj hk (d := 24) (n := 32) (by decide)).symm) hn

/-- What the callee leaks, from the caller's state. -/
theorem leak : openSLeak (nS u) = hLeak h := by
  have eK : bytesAt u.mem (u.gpr .rdi) 32 = bytesAt h.mem (h.gpr .rdi) 32 := by
    rw [hb.rdi]; exact hb.bytes_eq hs.b_k (by decide)
  have eN : bytesAt u.mem (u.gpr .rsi) 12 = bytesAt h.mem (h.gpr .rsi) 12 := by
    rw [hb.rsi]; exact hb.bytes_eq hs.b_n (by decide)
  have eA : bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat = bytesAt h.mem (h.gpr .rdx) (h.gpr .rcx).toNat := by
    rw [hb.rdx, hb.rcx]; exact hb.bytes_eq hs.b_a (Nat.le_of_lt (h.gpr .rcx).isLt)
  have eC : bytesAt u.mem (u.gpr .r11) (u.gpr .r9).toNat = bytesAt h.mem (hS h) (hL h) := by
    rw [hb.r11, hb.r9]; exact hb.bytes_eq hs.b_s (Nat.le_of_lt (h.gpr .r9).isLt)
  have eT : bytesAt u.mem (stackArg u 0) 16 = bytesAt h.mem (hT h) 16 := by
    rw [hb.arg0]; exact hb.bytes_eq hs.b_t (by decide)
  show [if (Spec.ChaCha20Poly1305.decrypt (bytesAt u.mem (u.gpr .rdi) 32) (bytesAt u.mem (u.gpr .rsi) 12)
    (bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat) (bytesAt u.mem (u.gpr .r11) (u.gpr .r9).toNat)
    (bytesAt u.mem (stackArg u 0) 16)).isSome then 1 else 0] = _
  rw [eK, eN, eA, eC, eT]; rfl

/-- What the callee decrypts, from the caller's state. -/
theorem post {z : State} (hp : openSPost (nS u) z) : hPost h z := by
  have eK : K (nS u) = bytesAt h.mem (h.gpr .rdi) 32 := by
    show bytesAt u.mem (u.gpr .rdi) 32 = _
    rw [hb.rdi]; exact hb.bytes_eq hs.b_k (by decide)
  have eN : N (nS u) = bytesAt h.mem (h.gpr .rsi) 12 := by
    show bytesAt u.mem (u.gpr .rsi) 12 = _
    rw [hb.rsi]; exact hb.bytes_eq hs.b_n (by decide)
  have eA : A (nS u) = bytesAt h.mem (h.gpr .rdx) (h.gpr .rcx).toNat := by
    show bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat = _
    rw [hb.rdx, hb.rcx]; exact hb.bytes_eq hs.b_a (Nat.le_of_lt (h.gpr .rcx).isLt)
  have eC : C (nS u) = bytesAt h.mem (hS h) (hL h) := by
    show bytesAt u.mem (u.gpr .r11) (u.gpr .r9).toNat = _
    rw [hb.r11, hb.r9]; exact hb.bytes_eq hs.b_s (Nat.le_of_lt (h.gpr .r9).isLt)
  have eT : T0 (nS u) = bytesAt h.mem (hT h) 16 := by
    show bytesAt u.mem (stackArg u 0) 16 = _
    rw [hb.arg0]; exact hb.bytes_eq hs.b_t (by decide)
  have eD : dp (nS u) = hD h := hb.r8
  have eL : L (nS u) = hL h := by show (u.gpr .r9).toNat = _; rw [hb.r9]
  unfold openSPost at hp
  unfold hPost
  rw [eK, eN, eA, eC, eT, eD, eL] at hp
  exact hp

end Entry

/-! ## The call -/

theorem pushed_frame {h : State} (hs : CPre h) :
    Frame [⟨hB h + BitVec.ofNat 64 32, 24⟩] h.mem (pushed frameRegs h).mem := by
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega_using [this]
  have pf := (pushRegs_mem h frameRegs (by decide) hn).1
  rw [sub_hB h (by decide)] at pf
  exact pf

/-- The destination keeps its bytes when the frame loses its own. -/
theorem dst_lost {h : State} (hs : CPre h) {m m' : Mem} (hf : Frame [⟨hB h + BitVec.ofNat 64 32, 24⟩] m m') :
    bytesAt m' (hD h) (hL h) = bytesAt m (hD h) (hL h) := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := hdR h) (fun r hr => ?_) (Nat.le_of_lt (h.gpr .r9).isLt)
    (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact (CPre.stk_disj hs.b_d (d := 32) (n := 24) (by decide)).symm

/-- The call, from a state satisfying `CPre`. -/
theorem callOpen_ok (v : XorImpl) {h : State} (hs : CPre h) :
    WP isa (callOpen v.callee v.poly) h (COut h) := by
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega_using [this]
  have hu := hs.entry
  have hB' := hs.hB_lt
  have hd := inner_xdepth v
  rw [callOpen_eq]
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.callF (k := sharedK) (inner_ok v) (SpSafe.of_all (inner_spSafe v)) (by omega_using [hd]) (hu.spre hs)
    (Covers.append_left (hu.rd_cov hs) (hu.wr_cov hs).right) (hu.wr_cov hs)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, g₂, post₂⟩ mx' => ?_
  have prsp : (pushed frameRegs h).gpr .rsp = hB h + BitVec.ofNat 64 32 := by
    rw [pushed_rsp, sub_hB h (by decide)]; rfl
  refine ⟨cs' _ calleeSaved_rsp, wr', fun m uk fm => ?_⟩
  -- The pop of `r11`, `rax` and `r10` loses their 24 bytes, in the stack.
  rw [show h.gpr .rsp - BitVec.ofNat 64 (8 * frameRegs.length) = hB h + BitVec.ofNat 64 32 from
    (pushed_rsp _ _).symm.trans prsp] at fm
  replace fm : Frame [⟨hB h + BitVec.ofNat 64 32, 24⟩] s'.mem m := fm
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, rd', pushed_rd],
    by rw [popped_wr, wr', pushed_wr]; rfl, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      rw [popped_rsp, cs' _ calleeSaved_rsp, prsp, Offset.add_ofNat_add_ofNat, rsp_eq h]
      rfl
    · have hra : r ≠ .r10 := by rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' hra, cs' r hr, pushed_gpr _ _ hr']
  · -- The pushes, the return address and the callee: within the stack, the
    -- destination and `work`.
    have f₂ := Frame.below_mono f' (b := 32) (by omega_using [hd]) (by decide)
    rw [prsp, show wrB (eS h) = [hdR h, hwR h] by show [dR (eS h), ctxR (eS h)] = _; rw [hu.ed, hu.ec]] at f₂
    simp only [below, BitVec.add_sub_cancel] at f₂
    refine Frame.trans (Frame.trans (Frame.sub (pushed_frame hs) fun r hr => ?_) (Frame.sub f₂ fun r hr => ?_))
      (fm.sub fun r hr => ?_)
    rotate_left 2
    · rw [List.mem_singleton.mp hr]
      exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true], Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true],
        Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨hdR h, by simp only [List.mem_cons, true_or], fun _ h => h⟩
      · exact ⟨hwR h, by simp only [List.mem_cons, true_or, or_true], fun _ h => h⟩
      · exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true],
          Region.sub_prefix (by decide)⟩
  · rw [popped_mxcsr, mx', pushed_mxcsr]
  · have e : (popped .r10 [Reg.r11, Reg.rax, Reg.r10].length s').gpr .rax = s₂.gpr .rax :=
      (popped_gpr _ _ _ (by decide) (by decide)).trans (g₂ .rax (by decide)).symm
    have hp := hu.post hs post₂
    unfold hPost at hp ⊢
    rw [e, dst_lost hs fm, ← m₂]
    exact hp

/-- `callOpen_ok`, and what the call leaves in the keystream area of `work`
(`hW`). -/
theorem callOpen_okK (v : XorImpl) {h : State} (hs : CPre h) :
    WP isa (callOpen v.callee v.poly) h fun z => COut h z ∧ KsLeftZ v (hW h) (hL h) h.mem z.mem := by
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega_using [this]
  have hu := hs.entry
  have hB' := hs.hB_lt
  have hd := inner_xdepth v
  rw [callOpen_eq]
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.callF (k := sharedKL v) (inner_okL v) (SpSafe.of_all (inner_spSafe v)) (by omega_using [hd]) (hu.spre hs)
    (Covers.append_left (hu.rd_cov hs) (hu.wr_cov hs).right) (hu.wr_cov hs)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, g₂, ⟨post₂, ks₂⟩⟩ mx' => ?_
  have prsp : (pushed frameRegs h).gpr .rsp = hB h + BitVec.ofNat 64 32 := by
    rw [pushed_rsp, sub_hB h (by decide)]; rfl
  refine ⟨cs' _ calleeSaved_rsp, wr', fun m uk fm => ?_⟩
  -- The pop of `r11`, `rax` and `r10` loses their 24 bytes, in the stack.
  rw [show h.gpr .rsp - BitVec.ofNat 64 (8 * frameRegs.length) = hB h + BitVec.ofNat 64 32 from
    (pushed_rsp _ _).symm.trans prsp] at fm
  replace fm : Frame [⟨hB h + BitVec.ofNat 64 32, 24⟩] s'.mem m := fm
  dsimp only
  refine ⟨⟨fun r hr => ?_, by rw [popped_rd, rd', pushed_rd],
    by rw [popped_wr, wr', pushed_wr]; rfl, ?_, ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      rw [popped_rsp, cs' _ calleeSaved_rsp, prsp, Offset.add_ofNat_add_ofNat, rsp_eq h]
      rfl
    · have hra : r ≠ .r10 := by rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' hra, cs' r hr, pushed_gpr _ _ hr']
  · -- The pushes, the return address and the callee: within the stack, the
    -- destination and `work`.
    have f₂ := Frame.below_mono f' (b := 32) (by omega_using [hd]) (by decide)
    rw [prsp, show wrB (eS h) = [hdR h, hwR h] by show [dR (eS h), ctxR (eS h)] = _; rw [hu.ed, hu.ec]] at f₂
    simp only [below, BitVec.add_sub_cancel] at f₂
    refine Frame.trans (Frame.trans (Frame.sub (pushed_frame hs) fun r hr => ?_) (Frame.sub f₂ fun r hr => ?_))
      (fm.sub fun r hr => ?_)
    rotate_left 2
    · rw [List.mem_singleton.mp hr]
      exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true], Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true],
        Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨hdR h, by simp only [List.mem_cons, true_or], fun _ h => h⟩
      · exact ⟨hwR h, by simp only [List.mem_cons, true_or, or_true], fun _ h => h⟩
      · exact ⟨hstk h, by simp only [List.mem_cons, true_or, or_true],
          Region.sub_prefix (by decide)⟩
  · rw [popped_mxcsr, mx', pushed_mxcsr]
  · have e : (popped .r10 [Reg.r11, Reg.rax, Reg.r10].length s').gpr .rax = s₂.gpr .rax :=
      (popped_gpr _ _ _ (by decide) (by decide)).trans (g₂ .rax (by decide)).symm
    have hp := hu.post hs post₂
    unfold hPost at hp ⊢
    rw [e, dst_lost hs fm, ← m₂]
    exact hp
  · -- The keystream area: as the callee left it, from `work` as the call found it.
    have ec : cx ((eS h).withRegions (rdB (eS h) ++ [srcR (eS h)]) (wrB (eS h))) = hW h :=
      (stackArg_wr _ _ _ 1).trans hu.arg1
    have eL : L ((eS h).withRegions (rdB (eS h) ++ [srcR (eS h)]) (wrB (eS h))) = hL h := by
      show ((eS h).gpr .r9).toNat = _; rw [hu.gpr _ (by decide)]
    have k₂ := ks₂
    simp only [ec, eL, State.withRegions_mem] at k₂
    rw [← m₂] at fm
    refine k₂.frame (rs := [⟨hB h + BitVec.ofNat 64 32, 24⟩]) fm (fun k hk r hr hc => ?_) hu.mem fun k hk r hr => ?_
    · -- The frame's lost bytes are on the stack, apart from `work`.
      rw [List.mem_singleton.mp hr] at hc
      refine CPre.stk_disj hs.b_w (d := 32) (n := 24) (by decide) _ hc ?_
      rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by have := hs.o_w; omega_using [this, hk])
    simp only [List.mem_singleton] at hr; subst hr
    intro hc
    refine CPre.stk_disj hs.b_w (d := 24) (n := 32) (by decide) _ hc ?_
    rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by have := hs.o_w; omega_using [this, hk])

/-- The call, in two runs from states satisfying `CPre` that agree on what it
reads. -/
theorem callOpen_rel (v : XorImpl) {h₁ h₂ : State} (p₁ : CPre h₁) (p₂ : CPre h₂) (hq : CPub h₁ h₂) :
    RelCT isa (Eq2 h₁ h₂) (callOpen v.callee v.poly) TT := by
  rw [callOpen_eq]
  refine RelCT.frame (R := TT) (fun _ _ e => by obtain ⟨rfl, rfl⟩ := e; exact hq.rsp) ?_
  refine RelCT.callEx (k := sharedK) (inner_ok v) (inner_ct v) fun x y ⟨s₁, s₂, ⟨e₁, e₂⟩, ex, ey⟩ => ?_
  subst ex ey
  subst s₁
  subst s₂
  have hu₁ := p₁.entry
  have hu₂ := p₂.entry
  have hB : hB h₁ = hB h₂ := by simp only [hB, hq.rsp]
  refine ⟨_, _, _, _, hu₁.spre p₁, hu₂.spre p₂, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
    Covers.append_left (hu₁.rd_cov p₁) (hu₁.wr_cov p₁).right, hu₁.wr_cov p₁,
    Covers.append_left (hu₂.rd_cov p₂) (hu₂.wr_cov p₂).right, hu₂.wr_cov p₂, ?_⟩
  · show (eS h₁).gpr .rdi = (eS h₂).gpr .rdi; rw [hu₁.rdi, hu₂.rdi, hq.rdi]
  · show (eS h₁).gpr .rsi = (eS h₂).gpr .rsi; rw [hu₁.rsi, hu₂.rsi, hq.rsi]
  · show (eS h₁).gpr .rdx = (eS h₂).gpr .rdx; rw [hu₁.rdx, hu₂.rdx, hq.rdx]
  · show (eS h₁).gpr .rcx = (eS h₂).gpr .rcx; rw [hu₁.rcx, hu₂.rcx, hq.rcx]
  · show (eS h₁).gpr .r8 = (eS h₂).gpr .r8; rw [hu₁.r8, hu₂.r8, hq.r8]
  · show (eS h₁).gpr .r9 = (eS h₂).gpr .r9; rw [hu₁.r9, hu₂.r9, hq.r9]
  · show (eS h₁).gpr .rsp = (eS h₂).gpr .rsp; rw [hu₁.rsp, hu₂.rsp, hB]
  · show stackArg (eS h₁) 0 = stackArg (eS h₂) 0; rw [hu₁.arg0, hu₂.arg0, hT, hT, hq.r10]
  · show stackArg (eS h₁) 1 = stackArg (eS h₂) 1; rw [hu₁.arg1, hu₂.arg1, hW, hW, hq.rax]
  · exact hq.mx
  · show (eS h₁).gpr .r11 = (eS h₂).gpr .r11; rw [hu₁.r11, hu₂.r11, hq.r11]
  · rw [hu₁.leak p₁, hu₂.leak p₂, hq.leak]
  · show ((pushed frameRegs h₁).gpr .rsp) = (pushed frameRegs h₂).gpr .rsp
    rw [pushed_rsp, pushed_rsp, hq.rsp]

end VG.Proof.ChaCha20Poly1305.X86_64.CallOpen

end

end

/-! # Shared small-message fallbacks, with their argument and stack frames -/

@[expose] public section
namespace VG.Proof.ChaCha20Poly1305.X86_64.Shared
open VG VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64 (XorImpl)
open VG.Impl.ChaCha20Poly1305.X86_64.Stitch (smallLim winLo winHi ifmaLo ifmaHi)

/-- Public contracts, including the extra forwarding frame and return address. -/
def contract (enc : Bool) (stack : Nat) : Contract isa :=
  if enc then Spec.ChaCha20Poly1305.sealContract abi stack
  else Spec.ChaCha20Poly1305.openZeroContract abi stack

theorem sat (enc : Bool) : ∃ s, (contract enc 1768).pre s := by
  cases enc
  · implies_sat [contract, Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
      Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, abi, argRegs]
      [openFrameSat, openSat] using openFrameSat
  · implies_sat [contract, Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Spec.ChaCha20Poly1305.sealPost, abi, argRegs] [sealFrameSat, sealSat] using sealFrameSat

/-- A larger reserved stack area implies the existing framed contract. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (h : (sig.contract abi pre post wa 1768 leak).pre s) :
    (sig.contract abi pre post wa 1752 leak).pre s := by
  rw [pre_args hk] at h ⊢
  obtain ⟨⟨hs, hwf⟩, hr, hw, hp, hd, hb, ht⟩ := h
  refine ⟨⟨?_, hwf⟩, hr, hw, hp, ?_, hb, ht⟩
  · right; rcases hs with hs | hs <;> omega
  · intro r hr a ha
    simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd _ (by simp) a ha
    · exact (hd (below (s.gpr .rsp) 1768) (by simp [stackBelow]) a ha).sub_left
        (below_sub (a := 1752) (b := 1768) (by decide) (by decide))

theorem pre_old (enc : Bool) {s : State} (h : (contract enc 1768).pre s) :
    (contract enc 1752).pre s := by
  cases enc
  · exact pre_stack (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h
  · exact pre_stack (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (leak := none) (by decide) h

theorem widen {c : Prog isa} (h : Verified target c (contract true 1752)) :
    Verified target c (contract true 1768) :=
  h.of_implies ⟨fun _ hp => pre_old true hp, fun _ _ _ hp => hp, fun _ _ _ _ hp => hp, sat true⟩

/-! ## `seal` -/

theorem body_verified (v : XorImpl) : Verified target (body v.callee v.poly) (contract true 1752) := by
  by_cases hv : v.poly = .avx2
  · have h := sealS_framed v hv
    simpa only [body, framed, contract, ↓reduceIte, hv] using h
  · simpa only [body, framed, contract, ↓reduceIte, hv] using seal_framed v

theorem body_sp (v : XorImpl) : (body v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  apply withStackArgScratchWipedX_spSafe
  by_cases hv : v.poly = .avx2
  · have h := sealS_spSafe v hv
    simpa only [↓reduceIte, hv] using h
  · simpa only [↓reduceIte, hv] using seal_spSafe v

theorem body_depth (v : XorImpl) : (body v.callee v.poly).x86_64Depth ≤ 1752 := by
  have hd : (if v.poly = .avx2 then Impl.ChaCha20Poly1305.X86_64.Stitch.sealStitched
        { v.callee with pass := 512 } .avx2 else Impl.ChaCha20Poly1305.X86_64.«seal» v.callee v.poly).x86_64Depth
        ≤ 24 := by
    by_cases hv : v.poly = .avx2
    · simpa only [↓reduceIte, hv] using sealS_xdepth v
    · simpa only [↓reduceIte, hv] using seal_xdepth v
  change max _ 0 + 1728 ≤ 1752
  rw [Nat.max_zero]
  exact Nat.add_le_add_right hd 1728

theorem call_sp (v : XorImpl) : (bodyCall v.callee v.poly).all (fun i => !isa.writesSp i) = true :=
  forward_spSafe (body_sp v)

theorem call_depth (v : XorImpl) : (bodyCall v.callee v.poly).x86_64Depth ≤ 1768 := by
  change max 0 (_ + 8) + 8 ≤ 1768
  rw [Nat.zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_right (body_depth v) 8) 8

theorem call_verified (v : XorImpl) : Verified target (bodyCall v.callee v.poly) (contract true 1768) :=
  Verified.forward (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8) (leak := none)
    (show Verified target _ (Spec.ChaCha20Poly1305.sealContract abi 1752) from body_verified v)
    (by decide) (by decide) (by decide) (by decide) (body_sp v) (body_depth v)
    (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp)
    (fun vs m₁ m₂ m' r hl hb _ hp => sealPost_local _ vs m₁ m₂ m' r hl hb hp)
    (fun vs m m₁ m₂ r hl _ hb _ hp => sealPost_out _ vs m m₁ m₂ r hl hb hp) (sat true)

theorem small_verified (v : XorImpl) (hv : v.poly = .avx2) :
    Verified target (smallCall v.callee) (contract true 1768) := by
  have h := call_verified v
  rwa [hv] at h

theorem large_sp (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode v.callee).all (fun i => !isa.writesSp i) = true := by
  have h := body_sp v
  rw [hv] at h
  have hc := call_sp v
  rw [hv] at hc
  unfold largeCode
  split
  · simpa only [body, reduceCtorEq, ↓reduceIte] using h
  · exact hc

theorem large_depth (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode v.callee).x86_64Depth ≤ 1768 := by
  have h := body_depth v
  rw [hv] at h
  have hc := call_depth v
  rw [hv] at hc
  unfold largeCode
  split
  · have h' := Nat.le_trans h (show 1752 ≤ 1768 by decide)
    simpa only [body, reduceCtorEq, ↓reduceIte] using h'
  · exact hc

theorem large_verified (v : XorImpl) (hv : v.poly = .avx512) :
    Verified target (largeCode v.callee) (contract true 1768) := by
  have h := widen (body_verified v)
  rw [hv] at h
  have hc := call_verified v
  rw [hv] at hc
  unfold largeCode
  split
  · simpa only [body, reduceCtorEq, ↓reduceIte] using h
  · exact hc

/-! The entry comparison changes no arguments, buffer, or calling-convention state. -/

theorem flags_args {s t : State} (h : FlagsOnly s t) (sig : Sig) :
    allArgs sig t = allArgs sig s := by
  simp only [allArgs, argRegs, List.map_cons, List.map_nil, h.rdi, h.rsi, h.rdx,
    h.rcx, h.r8, h.r9]
  rw [show stackArg t = stackArg s from funext h.arg]

theorem flags_regions {s t : State} (h : FlagsOnly s t) (sig : Sig) :
    allRegions sig t = allRegions sig s := by
  simp only [allRegions, bufRegions, argArea, flags_args h, h.mem, h.argAddr]

theorem flags_pre_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s t : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h : FlagsOnly s t)
    (hp : (sig.contract abi pre post wa stack leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre t := by
  rw [pre_args hk] at hp ⊢
  simpa only [flags_args h, flags_regions h, h.rsp, h.mem, h.rd, h.wr,
    bufRegions] using hp

theorem flags_pre (enc : Bool) {stack : Nat} {s t : State} (h : FlagsOnly s t)
    (hp : (contract enc stack).pre s) : (contract enc stack).pre t := by
  cases enc
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h hp
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (leak := none) (by decide) h hp

theorem flags_post_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s t z : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h : FlagsOnly s t)
    (hp : (sig.contract abi pre post wa stack leak).post t z) :
    (sig.contract abi pre post wa stack leak).post s z := by
  rw [post_args hk] at hp ⊢
  simpa only [flags_args h, h.mem] using hp

theorem flags_pub_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ t₁ t₂ : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h₁ : FlagsOnly s₁ t₁) (h₂ : FlagsOnly s₂ t₂)
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) :
    (sig.contract abi pre post wa stack leak).pub t₁ t₂ := by
  rw [pubL_args hk] at hp ⊢
  simpa only [flags_args h₁, flags_args h₂, h₁.rsp, h₂.rsp, h₁.mem, h₂.mem, h₁.mx, h₂.mx] using hp

theorem flags_post (enc : Bool) {stack : Nat} {s t z : State} (h : FlagsOnly s t)
    (hp : (contract enc stack).post t z) : (contract enc stack).post s z := by
  cases enc
  · exact flags_post_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (stack := stack) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h hp
  · exact flags_post_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (stack := stack) (leak := none) (by decide) h hp

theorem flags_pub (enc : Bool) {stack : Nat} {s₁ s₂ t₁ t₂ : State} (h₁ : FlagsOnly s₁ t₁)
    (h₂ : FlagsOnly s₂ t₂) (hp : (contract enc stack).pub s₁ s₂) : (contract enc stack).pub t₁ t₂ := by
  cases enc
  · exact flags_pub_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (stack := stack) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h₁ h₂ hp
  · exact flags_pub_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (stack := stack) (leak := none) (by decide) h₁ h₂ hp

theorem pub_len (enc : Bool) {stack : Nat} {s t : State} (h : (contract enc stack).pub s t) :
    s.gpr .r9 = t.gpr .r9 := by
  cases enc
  · simp only [contract, Bool.false_eq_true, ↓reduceIte] at h
    rw [Spec.ChaCha20Poly1305.openZeroContract, pubL_args (by decide)] at h
    have hh := h.2.1 5 (by decide)
    change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
    simpa only [BitVec.setWidth_eq] using hh
  · simp only [contract, ↓reduceIte] at h
    rw [Spec.ChaCha20Poly1305.sealContract, pubL_args (by decide)] at h
    have hh := h.2.1 5 (by decide)
    change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
    simpa only [BitVec.setWidth_eq] using hh

/-- A public length choice between two framed implementations of the same
contract `k`, which the comparison (changing only the flags, `rax` and
`r10`) keeps, and whose public data includes the length, `r9`. -/
theorem chooseK {k : Contract isa}
    (hpre : ∀ s t, FlagsOnly s t → k.pre s → k.pre t)
    (hpost : ∀ s t z, FlagsOnly s t → k.post t z → k.post s z)
    (hpub : ∀ s₁ s₂ t₁ t₂, FlagsOnly s₁ t₁ → FlagsOnly s₂ t₂ → k.pub s₁ s₂ → k.pub t₁ t₂)
    (hlen : ∀ s t, k.pub s t → s.gpr .r9 = t.gpr .r9) (hsat : ∃ s, k.pre s)
    {b : List Instr} {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified target a k) (hc : Verified target c k)
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified target (.seq (.block b) (Code.iteCold .b a c)) k := by
  have cmp (s : State) : ∃ u, execBlock isa b s = some (u, []) ∧
      isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u := by
    obtain ⟨t, u, he, hp⟩ := hb s
    have e := Exec.block_eq (T := target) he
    have hn := execBlock_trace_nil ht e
    exact ⟨u, hn ▸ e, hp⟩
  refine Verified.entryBranch (p := fun s => p (s.gpr .r9)) (fun _ => []) ha hc ?_ ?_ hsat
  · intro s hs
    obtain ⟨u, he, hp, hf⟩ := cmp s
    exact ⟨u, he, hp, fun _ => ⟨hpre _ _ hf hs,
      fun _ hA hP => ⟨hf.abi hA, hpost _ _ _ hf hP⟩⟩,
      fun _ => ⟨hpre _ _ hf hs, fun _ hA hP => ⟨hf.abi hA, hpost _ _ _ hf hP⟩⟩⟩
  · intro s t u v _ _ hp eu ev
    obtain ⟨u', eu', _, hf⟩ := cmp s
    obtain ⟨v', ev', _, hg⟩ := cmp t
    have ee := Option.some.inj (eu.symm.trans eu')
    have ef := Option.some.inj (ev.symm.trans ev')
    obtain rfl := (Prod.mk.inj ee).1
    obtain rfl := (Prod.mk.inj ef).1
    exact ⟨rfl, congrArg p (hlen _ _ hp), fun _ => hpub _ _ _ _ hf hg hp,
      fun _ => hpub _ _ _ _ hf hg hp⟩

/-- A public length choice between two framed implementations of the same API. -/
theorem choose (enc : Bool) {stack : Nat} (hsat : ∃ s, (contract enc stack).pre s) {b : List Instr}
    {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified target a (contract enc stack)) (hc : Verified target c (contract enc stack))
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified target (.seq (.block b) (Code.iteCold .b a c)) (contract enc stack) :=
  chooseK (fun _ _ hf hs => flags_pre enc hf hs) (fun _ _ _ hf hP => flags_post enc hf hP)
    (fun _ _ _ _ hf hg hp => flags_pub enc hf hg hp) (fun _ _ hp => pub_len enc hp) hsat ha hc hb ht

/-- The dispatch tests access no memory. -/
theorem small_trace (lim : Nat) : ∀ i ∈ Impl.ChaCha20Poly1305.X86_64.Stitch.smallTest lim,
    ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [Impl.ChaCha20Poly1305.X86_64.Stitch.smallTest, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem window_trace : ∀ i ∈ Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaTest,
    ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaTest, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem seal_verified (v : XorImpl) :
    Verified target (sealCode v.callee v.poly) (contract true 1768) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := small_verified v.small v.small_poly
    rw [XorImpl.small_callee] at hs
    have hg := large_verified v hb
    exact choose true (sat true) (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | _ =>
    have h := call_verified v
    rw [hb] at h
    exact h

theorem seal_sp (v : XorImpl) : (sealCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := call_sp v
  have hg : v.poly = .avx512 → (largeCode v.callee).all (fun i => !isa.writesSp i) = true := large_sp v
  have hs := call_sp v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  change (smallCall v.callee.small).all (fun i => !isa.writesSp i) = true at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := hg hb
    simp only [sealCode, Code.iteCold, Code.all, hs, hg, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | _ => rw [hb] at ho; exact ho

theorem seal_depth (v : XorImpl) : (sealCode v.callee v.poly).x86_64Depth ≤ 1768 := by
  have ho := call_depth v
  have hs := call_depth v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := large_depth v hb
    simp only [sealCode, Code.iteCold, Code.x86_64Depth, Nat.max_le]
    exact ⟨by decide, ⟨⟨by decide, by decide⟩, hs⟩, hg⟩
  | _ => rw [hb] at ho; exact ho

/-! ## `open`

`open`, in its frame of `work`, loads the arguments of the body and calls it
(`openCall`), as `open_to` does (`OpenTo.lean`): from `open`'s precondition
with the 56 bytes of stack the call uses (`openPre`), the state after the
loads satisfies what the call needs (`ocpre_of`: `CallOpen.CPre`), with the
data as the ciphertext. -/

/-- `open`'s precondition (`preX86_64 false`), with the 56 bytes of stack
below the return address that the call uses. -/
def openPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .rdi, 32⟩
  let nonce : Region := ⟨s.gpr .rsi, 12⟩
  let aad : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1696⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack : Region := ⟨s.gpr .rsp - 56, 56⟩
  s.rd = [key, nonce, aad, tag, args] ∧ s.wr = [data, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧ data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  ret.Disjoint work ∧ ret.Disjoint data ∧
  stack.Disjoint work ∧ stack.Disjoint key ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧
  stack.Disjoint data ∧ stack.Disjoint tag ∧
  (stackArg s 1).toNat + 1696 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64 ∧ 56 ≤ (s.gpr .rsp).toNat

/-- `open` in its frame of `work`, as the proofs state it. -/
def openK : Contract isa where
  pre := openPre
  post := openX86_64.post
  pub := openX86_64.pub

/-- After `openArgs`: the data's address, `work` and `tag` in `r11`, `rax`
and `r10`. -/
structure OLoaded (s h : State) : Prop where
  r11 : h.gpr .r11 = s.gpr .r8
  rax : h.gpr .rax = stackArg s 1
  r10 : h.gpr .r10 = stackArg s 0
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → h.gpr r = s.gpr r
  mem : h.mem = s.mem
  rd : h.rd = s.rd
  wr : h.wr = s.wr
  mx : h.mxcsr = s.mxcsr

theorem openArgs_ok {s : State} (hs : openPre s) : WP isa (.block openArgs) s (OLoaded s) := by
  obtain ⟨hrd, -⟩ := hs
  have hg : ∀ k, k + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 + k)) 8 := by
    intro k hk
    refine ⟨⟨stackArgAddr s 0, 16⟩, by rw [hrd]; simp, ?_⟩
    rw [off_eq, show s.gpr .rsp + BitVec.ofNat 64 (8 + k) = stackArgAddr s 0 + BitVec.ofNat 64 k by
      simp only [stackArgAddr, BitVec.ofNat_add, BitVec.add_assoc]]
    exact Offset.contains_base _ hk (by omega_using [hk])
  have h16 := hg 8 (by omega_using [])
  have h8 := hg 0 (by omega_using [])
  simp only [show 8 + 8 = 16 from rfl, show 8 + 0 = 8 from rfl] at h16 h8
  have e16 : s.mem.readW (off (s.gpr .rsp) 16) 64 = stackArg s 1 := by
    simp only [stackArg, stackArgAddr, off_eq]
  have e8 : s.mem.readW (off (s.gpr .rsp) 8) 64 = stackArg s 0 := by
    simp only [stackArg, stackArgAddr, off_eq]
  apply WP.of_runBlock
  simp only [openArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, ↓reduceIte, h16, h8,
    e16, e8, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [RegUpd.gpr_setReg], by simp [RegUpd.gpr_setReg], by simp [RegUpd.gpr_setReg],
    fun r h₁ h₂ h₃ => by simp [RegUpd.gpr_setReg, h₁, h₂, h₃], by simp [RegUpd.mem_setReg],
    by simp [RegUpd.rd_setReg], by simp [RegUpd.wr_setReg], by simp [RegUpd.mxcsr_setReg]⟩

namespace OLoaded

variable {s h : State} (hh : OLoaded s h)
include hh

theorem rsp : h.gpr .rsp = s.gpr .rsp := hh.keep _ (by decide) (by decide) (by decide)
theorem rdi : h.gpr .rdi = s.gpr .rdi := hh.keep _ (by decide) (by decide) (by decide)
theorem rsi : h.gpr .rsi = s.gpr .rsi := hh.keep _ (by decide) (by decide) (by decide)
theorem rdx : h.gpr .rdx = s.gpr .rdx := hh.keep _ (by decide) (by decide) (by decide)
theorem rcx : h.gpr .rcx = s.gpr .rcx := hh.keep _ (by decide) (by decide) (by decide)
theorem r8 : h.gpr .r8 = s.gpr .r8 := hh.keep _ (by decide) (by decide) (by decide)
theorem r9 : h.gpr .r9 = s.gpr .r9 := hh.keep _ (by decide) (by decide) (by decide)

theorem ek : CallOpen.hkR h = ⟨s.gpr .rdi, 32⟩ := by show (⟨h.gpr .rdi, 32⟩ : Region) = _; rw [hh.rdi]
theorem en : CallOpen.hnR h = ⟨s.gpr .rsi, 12⟩ := by show (⟨h.gpr .rsi, 12⟩ : Region) = _; rw [hh.rsi]
theorem ea : CallOpen.haR h = ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ := by
  show (⟨h.gpr .rdx, (h.gpr .rcx).toNat⟩ : Region) = _; rw [hh.rdx, hh.rcx]
theorem es : CallOpen.hsR h = ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
  show (⟨h.gpr .r11, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r11, hh.r9]
theorem ed : CallOpen.hdR h = ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
  show (⟨h.gpr .r8, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r8, hh.r9]
theorem et : CallOpen.htR h = ⟨stackArg s 0, 16⟩ := by show (⟨h.gpr .r10, 16⟩ : Region) = _; rw [hh.r10]
theorem ew : CallOpen.hwR h = ⟨stackArg s 1, 1696⟩ := by show (⟨h.gpr .rax, 1696⟩ : Region) = _; rw [hh.rax]
theorem eb : CallOpen.hstk h = ⟨s.gpr .rsp - 56, 56⟩ := by
  show (⟨h.gpr .rsp - BitVec.ofNat 64 56, 56⟩ : Region) = _; rw [hh.rsp]; rfl

end OLoaded

/-- The state after `openArgs` is ready for the call. -/
theorem ocpre_of {s h : State} (hs : openPre s) (hh : OLoaded s h) : CallOpen.CPre h := by
  obtain ⟨hrd, hwr, wk, wn, wa, wd, wt, dk, dn, da, dt, -, -, bw, bk, bn, ba, bd, bt, ow, oa, od, ot, ok, on,
    lo⟩ := hs
  refine ⟨by rw [hh.rsp]; exact lo, ?_, ?_, by rw [hh.ew, hh.ek]; exact wk, by rw [hh.ew, hh.en]; exact wn,
    by rw [hh.ew, hh.ea]; exact wa, by rw [hh.ew, hh.ed]; exact wd, by rw [hh.ew, hh.et]; exact wt,
    by rw [hh.ed, hh.ek]; exact dk, by rw [hh.ed, hh.en]; exact dn, by rw [hh.ed, hh.ea]; exact da,
    by rw [hh.ed, hh.et]; exact dt, by rw [hh.es, hh.ew]; exact wd.symm,
    .inl (by show h.gpr .r11 = h.gpr .r8; rw [hh.r11, hh.r8]),
    by rw [hh.eb, hh.ek]; exact bk, by rw [hh.eb, hh.en]; exact bn, by rw [hh.eb, hh.ea]; exact ba,
    by rw [hh.eb, hh.es]; exact bd, by rw [hh.eb, hh.ed]; exact bd, by rw [hh.eb, hh.et]; exact bt,
    by rw [hh.eb, hh.ew]; exact bw, by rw [hh.rdi]; exact ok, by rw [hh.rsi]; exact on,
    by rw [hh.rdx, hh.rcx]; exact oa, by show (h.gpr .r11).toNat + (h.gpr .r9).toNat ≤ _; rw [hh.r11, hh.r9]; exact od,
    by show (h.gpr .r8).toNat + (h.gpr .r9).toNat ≤ _; rw [hh.r8, hh.r9]; exact od,
    by show (h.gpr .r10).toNat + 16 ≤ _; rw [hh.r10]; exact ot,
    by show (h.gpr .rax).toNat + 1696 ≤ _; rw [hh.rax]; exact ow⟩
  · rw [hh.ek, hh.en, hh.ea, hh.et, hh.es, hh.rd, hh.wr, hrd, hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hh.ed, hh.ew, hh.wr, hwr]
    exact Covers.refl _

/-- The return address is apart from the stack below it. -/
theorem ret_stk (s : State) : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - 56, 56⟩ :=
  Offset.base_disjoint_below (n := 56) (k := 8) _ (by decide)

theorem openCall_correct (v : XorImpl) (s : State) (hs : openK.pre s) :
    ∃ t s', Exec isa (openCall v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ openK.post s s' := by
  have hs : openPre s := hs
  have rw' := hs.2.2.2.2.2.2.2.2.2.2.2
  refine WP.seq (WP.mono (openArgs_ok hs) fun h hh => ?_)
  refine WP.mono (CallOpen.callOpen_ok v (ocpre_of hs hh)) fun z hz => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [hz.cs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hh.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · -- The return address: apart from the data, `work` and the stack.
    have hf := hz.mem
    simp only [CallOpen.hdR, CallOpen.hwR, CallOpen.hstk, CallOpen.hB, CallOpen.hD, CallOpen.hW, CallOpen.hL,
      hh.r8, hh.rax, hh.r9, hh.rsp, hh.mem] at hf
    exact hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rw'.2.1
      · exact rw'.1
      · exact ret_stk s) (by decide)
  · rw [hz.mx, hh.mx]
  · have hp := hz.post
    unfold CallOpen.hPost at hp
    show openX86_64.post s z
    simp only [openX86_64]
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hD, CallOpen.hL, hh.r11,
      hh.r10, hh.r8, hh.r9] at hp
    exact hp

theorem openCall_ct (v : XorImpl) : ConstantTime isa openK.pre openK.pub (openCall v.callee v.poly) := by
  refine Gather.ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have p₁ : openPre σ₁ := p₁
  have p₂ : openPre σ₂ := p₂
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, qm⟩, ql⟩ := hq
  refine Gather.rel_seq (Gather.rel_regs [.rsp] (by simp [qsp]) ⟨_, by taint_decide⟩) (openArgs_ok p₁)
    (openArgs_ok p₂) fun h₁ h₂ hh₁ hh₂ => CallOpen.callOpen_rel v (ocpre_of p₁ hh₁) (ocpre_of p₂ hh₂)
      ⟨by rw [hh₁.rdi, hh₂.rdi, q₁], by rw [hh₁.rsi, hh₂.rsi, q₂], by rw [hh₁.rdx, hh₂.rdx, q₃],
        by rw [hh₁.rcx, hh₂.rcx, q₄], by rw [hh₁.r8, hh₂.r8, q₅], by rw [hh₁.r9, hh₂.r9, q₆],
        by rw [hh₁.r10, hh₂.r10, a₀], by rw [hh₁.r11, hh₂.r11, q₅],
        by rw [hh₁.rax, hh₂.rax, a₁], by rw [hh₁.rsp, hh₂.rsp, qsp], ?_,
        by rw [hh₁.mx, hh₂.mx, qm]⟩
  have leak : ∀ {σ h : State}, OLoaded σ h → CallOpen.hLeak h = openLeakX86_64 σ := fun {σ h} hh => by
    unfold CallOpen.hLeak openLeakX86_64
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hL, hh.r11, hh.r10, hh.r9]
  rw [leak hh₁, leak hh₂, ql]

/-- `open`'s call's contract on its working space is `openK`'s. -/
theorem openCall_implies : openK.Implies (openZeroScratchContract X86_64.abi 212 56) :=
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, X86_64.argRegs]
        simp only [openK, Proof.ChaCha20Poly1305.openX86_64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
          [openSat] using openSat }

theorem openCall_verified (v : XorImpl) :
    Verified X86_64.target (openCall v.callee v.poly) (openZeroScratchContract X86_64.abi 212 56) :=
  Verified.of_correct (k := openK) (openCall_correct v) (openCall_ct v) openCall_implies

theorem openCall_spSafe (v : XorImpl) : (openCall v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  simp only [openCall, Code.all, CallOpen.callOpen_spSafe v, Bool.and_true]
  decide

theorem openCall_xdepth (v : XorImpl) : (openCall v.callee v.poly).x86_64Depth ≤ 56 := by
  have h := CallOpen.callOpen_xdepth v
  simp only [openCall, Code.x86_64Depth, Nat.max_le]
  exact ⟨Nat.zero_le _, h⟩

theorem sat_open : ∃ s, (contract false 1784).pre s := by
  implies_sat [contract, Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, abi, argRegs]
    [openFrameSat, openSat] using openFrameSat

/-- `open` of the instance calling the implementation `v` of
`vg_chacha20_xor`, without a choice by the length, in its frame of `work`. -/
theorem framed_verified (v : XorImpl) :
    Verified target (framed (openCall v.callee v.poly)) (contract false 1784) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openZeroPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (leak := some (Spec.ChaCha20Poly1305.openLeak X86_64.abi.ptrBits))
    (bytes := 1728) (k := 42) (openCall_verified v) (by decide) (by decide) (by decide)
    (openCall_spSafe v) (openCall_xdepth v) (by decide) (pre_local _ _) (openZeroPost_local _)
    (openZeroPost_out _) sat_open (hleak := openLeak_local _)

theorem framed_sp (v : XorImpl) :
    (framed (openCall v.callee v.poly)).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratchWipedX_spSafe (openCall_spSafe v)

theorem open_verified (v : XorImpl) :
    Verified target (openCode v.callee v.poly) (contract false 1784) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := framed_verified v.small
    rw [XorImpl.small_callee, v.small_poly] at hs
    have hg := framed_verified v
    rw [hb] at hg
    have heq : Impl.ChaCha20Poly1305.X86_64.Stitch.openLim v.callee.small.vl =
        Impl.ChaCha20Poly1305.X86_64.Stitch.smallLim v.callee.small.vl := rfl
    rw [openCode, heq]
    exact choose false sat_open (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | ifma =>
    have hs := framed_verified XorImpl.avx512vl.small
    rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hs
    have hg := framed_verified v
    rw [hb] at hg
    exact choose false sat_open (p := fun n => decide (ifmaLo ≤ n.toNat ∧ n.toNat < ifmaHi)) hs hg
      cmpWin_ok window_trace
  | _ =>
    have h := framed_verified v
    rw [hb] at h
    exact h

theorem open_sp (v : XorImpl) : (openCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := framed_sp v
  have hs := framed_sp v.small
  have hw := framed_sp XorImpl.avx512vl.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hw
  change (framed (openCall Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2)).all
    (fun i => !isa.writesSp i) = true at hw
  cases hb : v.poly with
  | avx512 =>
    rw [hb] at ho
    simp only [openCode, Code.iteCold, Code.all, hs, ho, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | ifma =>
    rw [hb] at ho
    simp only [openCode, Code.iteCold, Code.all, hw, ho, Bool.and_true]
    decide
  | _ => rw [hb] at ho; exact ho

end VG.Proof.ChaCha20Poly1305.X86_64.Shared
