module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTail
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CallOpen
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.OpenTo
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTail
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CallOpen
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ChaCha20-Poly1305 decryption out of place, x86-64: `Verified`

`OpenTo.body` (`Impl/ChaCha20Poly1305/X86_64/OpenTo.lean`) loads the
arguments of `open`'s body and calls it (`Shared.callOpen`), as `open` does:
from what the contract of `vg_chacha20_poly1305_open_to` with its working
space gives (`TPre`), the state after the loads satisfies what the call needs
(`cpre_of`: `CallOpen.CPre`), and what the call does (`CallOpen.callOpen_ok`,
`CallOpen.callOpen_rel`, from the body's contract, proven once) is
`open_to`'s postcondition (`toPost`). Then `work` in a frame of its own
(`Verified.stackArgScratchWipedXPre`: the postcondition reads the
destination's `len` bytes, which the precondition makes `dst_len`), and the
AVX-512 instances' choice of the AVX2 code by the length, as `open`'s
(`Shared.chooseK`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.OpenTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.OpenTo
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_regs ct_of rel_frame)
open VG.Proof.ChaCha20.X86_64 (XorImpl)

/-! ## The entry state -/

section
variable (s : State)
/-- The arguments on entry. -/
abbrev eSrc : Addr := s.gpr .r8
abbrev eLn : Nat := (s.gpr .r9).toNat
abbrev eDst : Addr := stackArg s 0
abbrev eTg : Addr := stackArg s 2
abbrev eW : Addr := stackArg s 3
/-- Their regions (the destination's `len` bytes, which are `dst_len`), the
stack arguments, the return address, and the 56 bytes below it that the
call uses (`CallOpen.hstk`), from `fB`. -/
abbrev ekR : Region := ⟨s.gpr .rdi, 32⟩
abbrev enR : Region := ⟨s.gpr .rsi, 12⟩
abbrev eaR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev esR : Region := ⟨eSrc s, eLn s⟩
abbrev edR : Region := ⟨eDst s, eLn s⟩
abbrev etR : Region := ⟨eTg s, 16⟩
abbrev ewR : Region := ⟨eW s, 1696⟩
abbrev eargR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev eretR : Region := ⟨s.gpr .rsp, 8⟩
abbrev fB : Addr := s.gpr .rsp - BitVec.ofNat 64 56
abbrev estkR : Region := ⟨fB s, 56⟩
end

/-- What the contract of `vg_chacha20_poly1305_open_to` with `work` gives. -/
structure TPre (s : State) : Prop where
  sp_lo : 56 ≤ (s.gpr .rsp).toNat
  sp_hi : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  rd : s.rd = [ekR s, enR s, eaR s, esR s, etR s, eargR s]
  wr : s.wr = [⟨eDst s, (stackArg s 1).toNat⟩, ewR s]
  k_d : (ekR s).Disjoint (edR s)
  k_w : (ekR s).Disjoint (ewR s)
  n_d : (enR s).Disjoint (edR s)
  n_w : (enR s).Disjoint (ewR s)
  a_d : (eaR s).Disjoint (edR s)
  a_w : (eaR s).Disjoint (ewR s)
  s_d : (esR s).Disjoint (edR s)
  s_w : (esR s).Disjoint (ewR s)
  d_t : (edR s).Disjoint (etR s)
  d_w : (edR s).Disjoint (ewR s)
  d_g : (edR s).Disjoint (eargR s)
  t_w : (etR s).Disjoint (ewR s)
  w_g : (ewR s).Disjoint (eargR s)
  r_k : (eretR s).Disjoint (ekR s)
  r_n : (eretR s).Disjoint (enR s)
  r_a : (eretR s).Disjoint (eaR s)
  r_s : (eretR s).Disjoint (esR s)
  r_d : (eretR s).Disjoint (edR s)
  r_t : (eretR s).Disjoint (etR s)
  r_w : (eretR s).Disjoint (ewR s)
  r_g : (eretR s).Disjoint (eargR s)
  b_k : (estkR s).Disjoint (ekR s)
  b_n : (estkR s).Disjoint (enR s)
  b_a : (estkR s).Disjoint (eaR s)
  b_s : (estkR s).Disjoint (esR s)
  b_d : (estkR s).Disjoint (edR s)
  b_t : (estkR s).Disjoint (etR s)
  b_w : (estkR s).Disjoint (ewR s)
  b_g : (estkR s).Disjoint (eargR s)
  o_k : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64
  o_n : (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64
  o_a : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  o_s : (eSrc s).toNat + eLn s ≤ 2 ^ 64
  o_d : (eDst s).toNat + eLn s ≤ 2 ^ 64
  o_t : (eTg s).toNat + 16 ≤ 2 ^ 64
  o_w : (eW s).toNat + 1696 ≤ 2 ^ 64
  dl : (stackArg s 1).toNat = eLn s

/-- `open_to`'s result, through what it reads of the state on entry: `open`'s
(`Stitch.openPostAt`), with the ciphertext at `src` and the plaintext at
`dst`. -/
def toPost (s z : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (eSrc s) (eLn s))
      (bytesAt s.mem (eTg s) 16) with
  | some pt => (z.gpr .rax).setWidth 32 = 1 ∧ bytesAt z.mem (eDst s) (eLn s) = pt
  | none => (z.gpr .rax).setWidth 32 = 0 ∧ bytesAt z.mem (eDst s) (eLn s) = List.replicate (eLn s) 0

/-- What `open_to` may leak: whether the tag is right. -/
def toLeak (s : State) : List Nat :=
  [if (Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (eSrc s) (eLn s))
      (bytesAt s.mem (eTg s) 16)).isSome then 1 else 0]

/-- What two runs agree on: the arguments, the stack pointer, the stack
arguments, and whether the tag is right. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧ toLeak s₁ = toLeak s₂

/-- `vg_chacha20_poly1305_open_to(key, nonce, aad, aad_len, src, len, dst,
dst_len, tag, work) -> u32`, as the proofs state it. -/
def toK : Contract isa where
  pre := TPre
  post := toPost
  pub := toPub

namespace TPre

variable {s : State} (hs : TPre s)
include hs

/-- A stack argument is readable. -/
theorem arg_in {j : Nat} (hj : j < 4) : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * (j + 1))) 8 :=
  ⟨eargR s, by rw [hs.rd]; simp, by
    rw [off_eq]; exact Offset.contains _ (e := 8 * (0 + 1)) (by omega) (by omega) (by have := hs.sp_hi; omega)⟩

omit hs in
theorem arg_val (j : Nat) : s.mem.readW (off (s.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := by
  rw [off_eq]; rfl

end TPre

/-- After `toArgs`: `work`, `tag`, `src` and `dst` in `rax`, `r10`, `r11` and
`r8`. -/
structure Loaded (s h : State) : Prop where
  rax : h.gpr .rax = eW s
  r10 : h.gpr .r10 = eTg s
  r11 : h.gpr .r11 = eSrc s
  r8 : h.gpr .r8 = eDst s
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → r ≠ .r8 → h.gpr r = s.gpr r
  mem : h.mem = s.mem
  rd : h.rd = s.rd
  wr : h.wr = s.wr
  mx : h.mxcsr = s.mxcsr

theorem toArgs_ok {s : State} (hs : TPre s) : WP isa (.block toArgs) s (Loaded s) := by
  have r₃₂ := hs.arg_in (j := 3) (by decide)
  have r₂₄ := hs.arg_in (j := 2) (by decide)
  have r₈ := hs.arg_in (j := 0) (by decide)
  have v₃₂ := TPre.arg_val (s := s) 3
  have v₂₄ := TPre.arg_val (s := s) 2
  have v₈ := TPre.arg_val (s := s) 0
  simp only [Nat.reduceAdd, Nat.reduceMul] at r₃₂ r₂₄ r₈ v₃₂ v₂₄ v₈
  apply WP.of_runBlock
  simp only [toArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, r₃₂, r₂₄, r₈,
    v₃₂, v₂₄, v₈, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, h₁, h₂, h₃, h₄], by simp [mem_setReg], by simp [rd_setReg],
    by simp [wr_setReg], by simp [mxcsr_setReg]⟩

/-! ## The call -/

namespace Loaded

variable {s h : State} (hh : Loaded s h)
include hh

theorem rsp : h.gpr .rsp = s.gpr .rsp := hh.keep _ (by decide) (by decide) (by decide) (by decide)
theorem rdi : h.gpr .rdi = s.gpr .rdi := hh.keep _ (by decide) (by decide) (by decide) (by decide)
theorem rsi : h.gpr .rsi = s.gpr .rsi := hh.keep _ (by decide) (by decide) (by decide) (by decide)
theorem rdx : h.gpr .rdx = s.gpr .rdx := hh.keep _ (by decide) (by decide) (by decide) (by decide)
theorem rcx : h.gpr .rcx = s.gpr .rcx := hh.keep _ (by decide) (by decide) (by decide) (by decide)
theorem r9 : h.gpr .r9 = s.gpr .r9 := hh.keep _ (by decide) (by decide) (by decide) (by decide)

theorem ek : CallOpen.hkR h = ekR s := by show (⟨h.gpr .rdi, 32⟩ : Region) = _; rw [hh.rdi]
theorem en : CallOpen.hnR h = enR s := by show (⟨h.gpr .rsi, 12⟩ : Region) = _; rw [hh.rsi]
theorem ea : CallOpen.haR h = eaR s := by
  show (⟨h.gpr .rdx, (h.gpr .rcx).toNat⟩ : Region) = _; rw [hh.rdx, hh.rcx]
theorem es : CallOpen.hsR h = esR s := by
  show (⟨h.gpr .r11, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r11, hh.r9]
theorem ed : CallOpen.hdR h = edR s := by
  show (⟨h.gpr .r8, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r8, hh.r9]
theorem et : CallOpen.htR h = etR s := by show (⟨h.gpr .r10, 16⟩ : Region) = _; rw [hh.r10]
theorem ew : CallOpen.hwR h = ewR s := by show (⟨h.gpr .rax, 1696⟩ : Region) = _; rw [hh.rax]
theorem eb : CallOpen.hstk h = estkR s := by
  show (⟨h.gpr .rsp - BitVec.ofNat 64 56, 56⟩ : Region) = _; rw [hh.rsp]

end Loaded

/-- The state after `toArgs` is ready for the call. -/
theorem cpre_of {s h : State} (hs : TPre s) (hh : Loaded s h) : CallOpen.CPre h := by
  have hd := hs.dl
  refine ⟨by rw [hh.rsp]; exact hs.sp_lo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, .inr ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hh.ek, hh.en, hh.ea, hh.es, hh.ed, hh.et, hh.ew, hh.eb, CallOpen.hS, CallOpen.hD,
      CallOpen.hT, CallOpen.hW, CallOpen.hL, hh.r11, hh.r8, hh.r10, hh.rax, hh.rdi, hh.rsi, hh.rdx, hh.rcx, hh.r9]
  · rw [hh.rd, hh.wr, hs.rd]
    exact Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  · rw [hh.wr, hs.wr, hd]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  · exact hs.k_w.symm
  · exact hs.n_w.symm
  · exact hs.a_w.symm
  · exact hs.d_w.symm
  · exact hs.t_w.symm
  · exact hs.k_d.symm
  · exact hs.n_d.symm
  · exact hs.a_d.symm
  · exact hs.d_t
  · exact hs.s_w
  · exact hs.s_d.symm
  · exact hs.b_k
  · exact hs.b_n
  · exact hs.b_a
  · exact hs.b_s
  · exact hs.b_d
  · exact hs.b_t
  · exact hs.b_w
  · exact hs.o_k
  · exact hs.o_n
  · exact hs.o_a
  · exact hs.o_s
  · exact hs.o_d
  · exact hs.o_t
  · exact hs.o_w

/-- The return address, at `fB + 56`, is apart from the stack below it. -/
theorem ret_stk {s : State} (hs : TPre s) : (eretR s).Disjoint (estkR s) := by
  have := hs.sp_lo
  show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 56, 56⟩
  exact Offset.base_disjoint_below _ (by have := hs.sp_hi; omega)

/-! ## The body -/

theorem body_correct (v : XorImpl) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa (body v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ toK.post s s' := by
  have hs : TPre s := hs
  refine WP.seq (WP.mono (toArgs_ok hs) fun h hh => ?_)
  refine WP.mono (CallOpen.callOpen_ok v (cpre_of hs hh)) fun z hz => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [hz.cs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hh.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · -- The return address: apart from the destination, `work` and the stack.
    have hf := hz.mem
    rw [hh.ed, hh.ew, hh.eb, hh.mem] at hf
    exact hf.readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.r_d
      · exact hs.r_w
      · exact ret_stk hs) (by decide)
  · rw [hz.mx, hh.mx]
  · have hp := hz.post
    unfold CallOpen.hPost at hp
    show toPost s z
    unfold toPost
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hD, CallOpen.hL, hh.r11,
      hh.r10, hh.r8, hh.r9] at hp
    exact hp

theorem body_ct (v : XorImpl) : ConstantTime isa toK.pre toK.pub (body v.callee v.poly) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have p₁ : TPre σ₁ := p₁
  have p₂ : TPre σ₂ := p₂
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, ql⟩ := hq
  refine rel_seq (rel_regs [.rsp] (by simp [qsp]) ⟨_, by taint_decide⟩) (toArgs_ok p₁) (toArgs_ok p₂)
    fun h₁ h₂ hh₁ hh₂ => CallOpen.callOpen_rel v (cpre_of p₁ hh₁) (cpre_of p₂ hh₂)
      ⟨by rw [hh₁.rdi, hh₂.rdi, q₁], by rw [hh₁.rsi, hh₂.rsi, q₂], by rw [hh₁.rdx, hh₂.rdx, q₃],
        by rw [hh₁.rcx, hh₂.rcx, q₄], by rw [hh₁.r8, hh₂.r8, eDst, eDst, a₀], by rw [hh₁.r9, hh₂.r9, q₆],
        by rw [hh₁.r10, hh₂.r10, eTg, eTg, a₂], by rw [hh₁.r11, hh₂.r11, eSrc, eSrc, q₅],
        by rw [hh₁.rax, hh₂.rax, eW, eW, a₃], by rw [hh₁.rsp, hh₂.rsp, qsp], ?_⟩
  have leak : ∀ {σ h : State}, Loaded σ h → CallOpen.hLeak h = toLeak σ := fun {σ h} hh => by
    unfold CallOpen.hLeak toLeak
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hL, hh.r11, hh.r10, hh.r9]
  rw [leak hh₁, leak hh₂, ql]

theorem body_spSafe (v : XorImpl) : (body v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  simp only [body, Code.all, CallOpen.callOpen_spSafe v, Bool.and_true]
  decide

theorem body_xdepth (v : XorImpl) : (body v.callee v.poly).x86_64Depth ≤ 56 := by
  have h := CallOpen.callOpen_xdepth v
  simp only [body, Code.x86_64Depth, Nat.max_le]
  exact ⟨Nat.zero_le _, h⟩

/-! ## The contract -/

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem tpre_of_spec {s : State} (h : (openToScratchContract X86_64.abi 212 56).pre s) : TPre s := by
  sig_pre [openToScratchContract, openToScratchSig, Spec.ChaCha20Poly1305.openToPre, X86_64.abi,
    X86_64.argRegs, stackArgs_four, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Gather.pairFacts_ro _ (by simp)] at h
  simp only [List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, Gather.filter_true', Gather.filter_false',
    Gather.filterMap_some', Gather.filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map,
    Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    Sig.conj, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, List.cons_append,
    List.singleton_append] at h
  obtain ⟨lo, hi, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, dg, tw, wg⟩, rk, rn, ra, rs, rdd, rt, rw,
    rg, bk, bn, ba, bs, bd, bt, bw, bg, ok, on, oa, os, od, ot, ow, dl, -⟩ := h
  rw [dl] at kd nd ad sd dt dw dg rdd bd od
  exact ⟨lo, hi, rd, wr, kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, dg, tw, wg, rk, rn, ra, rs, rdd, rt, rw, rg,
    bk, bn, ba, bs, bd, bt, bw, bg, ok, on, oa, os, od, ot, ow, dl⟩

theorem pub_of {s₁ s₂ : State} (hp : (openToScratchContract X86_64.abi 212 56).pub s₁ s₂) : toPub s₁ s₂ := by
  sig_pub [openToScratchContract, openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
    Spec.ChaCha20Poly1305.openToLeak, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨qsp, ql, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, ql⟩

/-- A state satisfying the precondition, with its working space: no
additional data or data, `dst` at `0x3000`, `tag` at `0x4000` and `work`
at 0, the stack arguments at `0x8008`. -/
def toSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x1100 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8009 then 0x30 else bif Nat.beq a.toNat 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩, ⟨0x8008, 32⟩]
  wr := [⟨0x3000, 0⟩, ⟨0, 1696⟩]

theorem toSat_pre : ∃ s, (openToScratchContract X86_64.abi 212 56).pre s := by
  refine ⟨toSat, ?_⟩
  sig_pre [openToScratchContract, openToScratchSig, Spec.ChaCha20Poly1305.openToPre, X86_64.abi,
    X86_64.argRegs, stackArgs_four, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem to_implies : toK.Implies (openToScratchContract X86_64.abi 212 56) where
  pre _ h := tpre_of_spec h
  post s s' _ h := by
    sig_eval [openToScratchContract, openToScratchSig, Spec.ChaCha20Poly1305.openToPost, X86_64.abi,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, X86_64.argRegs]
    simp only [toK, toPost] at h
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
  pub _ _ _ _ h := pub_of h
  sat := toSat_pre

theorem body_verified (v : XorImpl) :
    Verified X86_64.target (body v.callee v.poly) (openToScratchContract X86_64.abi 212 56) :=
  Verified.of_correct (k := toK) (body_correct v) (body_ct v) to_implies

/-! ## The frame of `work` -/

/-- A state satisfying the precondition, without the working space. -/
def toFrameSat : State :=
  { toSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩, ⟨0x8008, 24⟩],
               wr := [⟨0x3000, 0⟩] }

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem toFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800).pre s := by
  refine ⟨toFrameSat, ?_⟩
  sig_pre [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- `vg_chacha20_poly1305_open_to` of the instance calling the
implementation `v` of `vg_chacha20_xor`, without a choice by the length,
with its working space in a frame of its own. -/
theorem scratched_verified (v : XorImpl) :
    Verified X86_64.target (scratched (body v.callee v.poly))
      (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800) :=
  X86_64.Verified.stackArgScratchWipedXPre (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 212) (pre := Spec.ChaCha20Poly1305.openToPre X86_64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (leak := some (Spec.ChaCha20Poly1305.openToLeak X86_64.abi.ptrBits))
    (bytes := 1744) (k := 42) (body_verified v) (by decide) (by decide) (by decide)
    (body_spSafe v) (body_xdepth v) (by decide) (openToPre_local _) (openToPost_local _) (openToPost_out _)
    toFrameSat_pre (hleak := openToLeak_local _)

theorem scratched_spSafe (v : XorImpl) :
    (scratched (body v.callee v.poly)).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratchWipedX_spSafe (body_spSafe v)

/-! ## The instances

As `open`'s (`Shared.open_verified`): the AVX-512 instances choose by the
length, before allocating `work`, the AVX2 code with `vg_chacha20_xor_avx2`'s or
`vg_chacha20_xor_avx512vl`'s rounds. -/

theorem pub_len {s t : State} (h : (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800).pub s t) :
    s.gpr .r9 = t.gpr .r9 := by
  rw [Spec.ChaCha20Poly1305.openToContract, pubL_args (by decide)] at h
  have hh := h.2.1 5 (by decide)
  change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
  simpa only [BitVec.setWidth_eq] using hh

/-- A public length choice between two framed implementations. -/
theorem choose {b : List Instr} {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified X86_64.target a (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800))
    (hc : Verified X86_64.target c (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800))
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified X86_64.target (.seq (.block b) (Code.iteCold .b a c))
      (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800) :=
  Shared.chooseK
    (fun _ _ hf hs => Shared.flags_pre_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1800) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hs)
    (fun _ _ _ hf hP => Shared.flags_post_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1800) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hP)
    (fun _ _ _ _ hf hg hp => Shared.flags_pub_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1800) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hg hp)
    (fun _ _ hp => pub_len hp) toFrameSat_pre ha hc hb ht

/-- `vg_chacha20_poly1305_open_to` of the instance calling the
implementation `v` of `vg_chacha20_xor`. -/
theorem openTo_verified (v : XorImpl) :
    Verified X86_64.target (openToCode v.callee v.poly) (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1800) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := scratched_verified v.small
    rw [XorImpl.small_callee, v.small_poly] at hs
    have hg := scratched_verified v
    rw [hb] at hg
    have heq : Stitch.openLim v.callee.small.vl = Stitch.smallLim v.callee.small.vl := rfl
    rw [openToCode, heq]
    exact choose (p := fun n => decide (n.toNat < Stitch.smallLim v.callee.small.vl ∨
      (Stitch.winLo ≤ n.toNat ∧ n.toNat < Stitch.winHi))) hs hg (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (Shared.small_trace _)
  | ifma =>
    have hs := scratched_verified XorImpl.avx512vl.small
    rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hs
    have hg := scratched_verified v
    rw [hb] at hg
    exact choose (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) hs hg
      Stitch.cmpWin_ok Shared.window_trace
  | _ =>
    have h := scratched_verified v
    rw [hb] at h
    exact h

theorem openTo_sp (v : XorImpl) : (openToCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := scratched_spSafe v
  have hs := scratched_spSafe v.small
  have hw := scratched_spSafe XorImpl.avx512vl.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hw
  change (scratched (body Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2)).all
    (fun i => !isa.writesSp i) = true at hw
  cases hb : v.poly with
  | avx512 =>
    rw [hb] at ho
    simp only [openToCode, Code.iteCold, Code.all, hs, ho, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | ifma =>
    rw [hb] at ho
    simp only [openToCode, Code.iteCold, Code.all, hw, ho, Bool.and_true]
    decide
  | _ => rw [hb] at ho; exact ho

end VG.Proof.ChaCha20Poly1305.X86_64.OpenTo
