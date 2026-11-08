module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTail
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTail
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

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
    h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := hp
  exact ⟨⟨more, h1⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

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
      Nat.max_le] at hc ha ⊢ <;>
    omega_arith
  · rw [inner_shared v hv]
    simp only [Impl.ChaCha20.X86_64.Callee.inPlace, openShared, openBody, openTail, zeroData, prologue,
      prologueA, prologueB, zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks, padRest, padCopy,
      padTail, crypt, cryptBig, cryptPre, xorKs, callX, Bool.cond_true, Impl.ChaCha20.X86_64.Xor.callTo,
      absorbLengths, finalizeTo, finalizeWith, Code.x86_64Depth, xorBufTo_xdepth, foldM_xdepth, init_xdepth,
      finalize_xdepth, Nat.max_le] at hc ha ⊢
    omega

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
  rw [toNat_sub_ofNat (by omega)]; omega

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
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega
  have hB' := hs.hB_lt
  obtain ⟨pf, pw⟩ := pushRegs_mem h frameRegs (by decide) hn
  rw [sub_hB h (by decide)] at pf
  have pw' : ∀ j (hj : j < 3) (d : Nat), d + 8 * (j + 1) = 56 →
      (pushed frameRegs h).mem.readW (hB h + BitVec.ofNat 64 d) 64 = h.gpr frameRegs[j] := by
    intro j hj d hd
    have := pw j hj
    rw [sub_hB h (by omega), show 56 - 8 * (j + 1) = d by omega] at this
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
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)
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
    hs.o_w, hs.o_a, hs.o_d, hs.o_t, hs.o_k, hs.o_n⟩

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
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega
  have pf := (pushRegs_mem h frameRegs (by decide) hn).1
  rw [sub_hB h (by decide)] at pf
  exact pf

/-- The call, from a state satisfying `CPre`. -/
theorem callOpen_ok (v : XorImpl) {h : State} (hs : CPre h) :
    WP isa (callOpen v.callee v.poly) h (COut h) := by
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by have := hs.sp_lo; simp; omega
  have hu := hs.entry
  have hB' := hs.hB_lt
  have hd := inner_xdepth v
  rw [callOpen_eq]
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.callF (k := sharedK) (inner_ok v) (SpSafe.of_all (inner_spSafe v)) (by omega) (hu.spre hs)
    (Covers.append_left (hu.rd_cov hs) (hu.wr_cov hs).right) (hu.wr_cov hs)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, g₂, post₂⟩ mx' => ?_
  have prsp : (pushed frameRegs h).gpr .rsp = hB h + BitVec.ofNat 64 32 := by
    rw [pushed_rsp, sub_hB h (by decide)]; rfl
  refine ⟨cs' _ calleeSaved_rsp, wr', ⟨fun r hr => ?_, by rw [popped_rd, rd', pushed_rd],
    by rw [popped_wr, wr', pushed_wr]; rfl, ?_, ?_, ?_⟩⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      rw [popped_rsp, cs' _ calleeSaved_rsp, prsp, Offset.add_ofNat_add_ofNat, rsp_eq h]
      rfl
    · have hra : r ≠ .r10 := by rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' hra, cs' r hr, pushed_gpr _ _ hr']
  · -- The pushes, the return address and the callee: within the stack, the
    -- destination and `work`.
    rw [popped_mem]
    have f₂ := Frame.below_mono f' (b := 32) (by omega) (by decide)
    rw [prsp, show wrB (eS h) = [hdR h, hwR h] by show [dR (eS h), ctxR (eS h)] = _; rw [hu.ed, hu.ec]] at f₂
    simp only [below, BitVec.add_sub_cancel] at f₂
    refine Frame.trans (Frame.sub (pushed_frame hs) fun r hr => ?_) (Frame.sub f₂ fun r hr => ?_)
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
    rw [popped_mem, ← m₂, e]
    exact hp

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
  refine ⟨_, _, _, _, hu₁.spre p₁, hu₂.spre p₂, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
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
  · show (eS h₁).gpr .r11 = (eS h₂).gpr .r11; rw [hu₁.r11, hu₂.r11, hq.r11]
  · rw [hu₁.leak p₁, hu₂.leak p₂, hq.leak]
  · show ((pushed frameRegs h₁).gpr .rsp) = (pushed frameRegs h₂).gpr .rsp
    rw [pushed_rsp, pushed_rsp, hq.rsp]

end VG.Proof.ChaCha20Poly1305.X86_64.CallOpen
