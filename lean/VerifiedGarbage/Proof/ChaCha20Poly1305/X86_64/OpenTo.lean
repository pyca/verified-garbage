module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTail
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

`OpenTo.body` (`Impl/ChaCha20Poly1305/X86_64/OpenTo.lean`) runs `open`'s
shared code (`openShared`, or the stitched `openStitchedShared`, verified
against `sharedK`: `OpenTail.lean`) inline, in a frame laid out as `open`'s
entry (`framed`), with the state's permissions narrowed to `open`'s regions
and the ciphertext's (`WP.inlineF`, `relCT_inline`). From what the contract
of `vg_chacha20_poly1305_open_to` with its working space gives (`TPre`), the
frame's state satisfies `sharedK`'s precondition (`Body.spre`), and its
postcondition is `open_to`'s (`toPost`). Then `work` in a frame of its own
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
stack arguments, the return address, and the 48 bytes below it that the
frame (24) and `open`'s calls (24) use, from `fB`. -/
abbrev ekR : Region := ⟨s.gpr .rdi, 32⟩
abbrev enR : Region := ⟨s.gpr .rsi, 12⟩
abbrev eaR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev esR : Region := ⟨eSrc s, eLn s⟩
abbrev edR : Region := ⟨eDst s, eLn s⟩
abbrev etR : Region := ⟨eTg s, 16⟩
abbrev ewR : Region := ⟨eW s, 1696⟩
abbrev eargR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev eretR : Region := ⟨s.gpr .rsp, 8⟩
abbrev fB : Addr := s.gpr .rsp - BitVec.ofNat 64 48
abbrev estkR : Region := ⟨fB s, 48⟩
end

/-- What the contract of `vg_chacha20_poly1305_open_to` with `work` gives. -/
structure TPre (s : State) : Prop where
  sp_lo : 48 ≤ (s.gpr .rsp).toNat
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

/-! ## The frame -/

namespace TPre

variable {s : State} (hs : TPre s)
include hs

theorem fB_lt : (fB s).toNat + 88 ≤ 2 ^ 64 := by
  have := hs.sp_lo; have := hs.sp_hi
  rw [toNat_sub_ofNat (by omega)]; omega

omit hs in
theorem rsp_eq : s.gpr .rsp = fB s + BitVec.ofNat 64 48 := (BitVec.sub_add_cancel _ _).symm

omit hs in
/-- A part of the 48 bytes of stack is apart from a region apart from all of
them. -/
theorem stk_disj {r : Region} (h : (estkR s).Disjoint r) {d n : Nat} (hd : d + n ≤ 48) :
    (⟨fB s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  h.sub_left (Offset.sub_base _ hd)

omit hs in
theorem stk0 {r : Region} (h : (estkR s).Disjoint r) {n : Nat} (hn : n ≤ 48) :
    (⟨fB s, n⟩ : Region).Disjoint r :=
  h.sub_left (Region.sub_prefix hn)

/-- The return address, at `fB + 48`, is apart from the stack below it. -/
theorem ret_stk {d n : Nat} (hd : d + n ≤ 48) :
    (eretR s).Disjoint ⟨fB s + BitVec.ofNat 64 d, n⟩ := by
  have := hs.fB_lt
  show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint _
  rw [rsp_eq]; exact Offset.disjoint _ (.inr hd) (by omega) (by omega)

omit hs in
theorem arg_contains {j : Nat} (hj : j < 4) : (eargR s).Contains (off (s.gpr .rsp) (8 * (j + 1))) 8 := by
  rw [off_eq]; exact Offset.contains _ (e := 8 * (0 + 1)) (by omega) (by omega) (by omega)

/-- A stack argument is readable. -/
theorem arg_in {j : Nat} (hj : j < 4) : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * (j + 1))) 8 :=
  ⟨eargR s, by rw [hs.rd]; simp, arg_contains hj⟩

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

/-- The registers the frame pushes. -/
abbrev frameRegs : List Reg := [.rax, .r10, .r11]

/-- The state `open`'s shared code starts in: after the frame's push. -/
structure Body (s u : State) : Prop where
  rdi : u.gpr .rdi = s.gpr .rdi
  rsi : u.gpr .rsi = s.gpr .rsi
  rdx : u.gpr .rdx = s.gpr .rdx
  rcx : u.gpr .rcx = s.gpr .rcx
  r8 : u.gpr .r8 = eDst s
  r9 : u.gpr .r9 = s.gpr .r9
  r11 : u.gpr .r11 = eSrc s
  rsp : u.gpr .rsp = fB s + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → u.gpr r = s.gpr r
  a0 : u.mem.readW (fB s + BitVec.ofNat 64 32) 64 = eTg s
  a1 : u.mem.readW (fB s + BitVec.ofNat 64 40) 64 = eW s
  mem : Frame [⟨fB s + BitVec.ofNat 64 24, 24⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = ⟨fB s + BitVec.ofNat 64 24, 24⟩ :: s.wr
  mx : u.mxcsr = s.mxcsr

theorem sub_fB (s : State) {a : Nat} (h : a ≤ 48) :
    s.gpr .rsp - BitVec.ofNat 64 a = fB s + BitVec.ofNat 64 (48 - a) := Offset.sub_ofNat_eq _ h

theorem body_of {s h : State} (hs : TPre s) (hh : Loaded s h) : Body s (pushed frameRegs h) := by
  have hsp : h.gpr .rsp = s.gpr .rsp := hh.keep _ (by decide) (by decide) (by decide) (by decide)
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp]; have := hs.sp_lo; simp; omega
  obtain ⟨pf, pw⟩ := pushRegs_mem h frameRegs (by decide) hn
  rw [hsp, sub_fB s (by decide)] at pf
  have pw' : ∀ j (hj : j < 3) (d : Nat), d + 8 * (j + 1) = 48 →
      (pushed frameRegs h).mem.readW (fB s + BitVec.ofNat 64 d) 64 = h.gpr frameRegs[j] := by
    intro j hj d hd
    have := pw j hj
    rw [hsp, sub_fB s (by omega), show 48 - 8 * (j + 1) = d by omega] at this
    exact this
  have ga : ∀ r, r ≠ .rsp → (pushed frameRegs h).gpr r = h.gpr r := fun r hr => pushed_gpr _ _ hr
  have kp : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → r ≠ .r8 → r ≠ .rsp → (pushed frameRegs h).gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [ga r h₅, hh.keep r h₁ h₂ h₃ h₄]
  refine ⟨kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [ga _ (by decide), hh.r8], kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [ga _ (by decide), hh.r11], ?_, fun r hr hr' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pushed_rsp, hsp, sub_fB s (by decide)]; rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact kp r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hr'
  · rw [pw' 1 (by decide) 32 (by decide)]; exact hh.r10
  · rw [pw' 0 (by decide) 40 (by decide)]; exact hh.rax
  · rw [← hh.mem]; exact pf
  · rw [pushed_rd, hh.rd]
  · rw [pushed_wr, hsp, sub_fB s (show 8 * frameRegs.length ≤ 48 by decide), hh.wr]
    rfl
  · rw [pushed_mxcsr, hh.mx]

/-! ## The shared code's precondition, narrowed -/

theorem stackArg_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArg (s.withRegions rd wr) j = stackArg s j := rfl
theorem stackArgAddr_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArgAddr (s.withRegions rd wr) j = stackArgAddr s j := rfl

/-- What the shared code may read and write, narrowed from the frame's
state: `open`'s regions, and the ciphertext. -/
abbrev rdB (u : State) : List Region := [kR u, nR u, aR u, tR u, argR u]
abbrev wrB (u : State) : List Region := [dR u, ctxR u]
abbrev srcR (u : State) : Region := ⟨sp u, L u⟩

theorem sub24 (B : Addr) : B + BitVec.ofNat 64 24 - 24 = B := BitVec.add_sub_cancel _ _
theorem sub24' (B : Addr) : B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24 = B := BitVec.add_sub_cancel _ _

namespace Body

variable {s u : State} (hb : Body s u)
include hb

theorem addr (j : Nat) : stackArgAddr u j = fB s + BitVec.ofNat 64 (24 + 8 * (j + 1)) := by
  show u.gpr .rsp + _ = _
  rw [hb.rsp, Offset.add_ofNat_add_ofNat]

theorem arg0 : stackArg u 0 = eTg s := by
  show u.mem.readW (stackArgAddr u 0) 64 = _; rw [hb.addr]; exact hb.a0
theorem arg1 : stackArg u 1 = eW s := by
  show u.mem.readW (stackArgAddr u 1) 64 = _; rw [hb.addr]; exact hb.a1

variable (hs : TPre s)
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
  refine ⟨hs.k_w.symm, hs.n_w.symm, hs.a_w.symm, hs.d_w.symm, hs.t_w.symm,
    (TPre.stk_disj hs.b_w (d := 32) (n := 16) (by decide)).symm, hs.k_d.symm, hs.n_d.symm, hs.a_d.symm, hs.d_t,
    (TPre.stk_disj hs.b_d (d := 32) (n := 16) (by decide)).symm,
    TPre.stk_disj hs.b_w (d := 24) (n := 8) (by decide), TPre.stk_disj hs.b_a (d := 24) (n := 8) (by decide),
    TPre.stk_disj hs.b_d (d := 24) (n := 8) (by decide), TPre.stk_disj hs.b_t (d := 24) (n := 8) (by decide),
    TPre.stk0 hs.b_w (by decide), TPre.stk0 hs.b_k (by decide), TPre.stk0 hs.b_n (by decide),
    TPre.stk0 hs.b_a (by decide), TPre.stk0 hs.b_d (by decide), TPre.stk0 hs.b_t (by decide),
    hs.o_w, hs.o_a, hs.o_d, hs.o_t, hs.o_k, hs.o_n⟩

/-- The shared code's precondition, narrowed. -/
theorem spre : SPreO (u.withRegions (rdB u ++ [srcR u]) (wrB u)) := by
  have hp := APre.of_more (more := [srcR u]) (hb.pre hs)
  have hB := hs.fB_lt
  refine ⟨hp, ⟨?_, ?_, ?_, ?_, Covers.of_mem fun r hr => ?_⟩, .inr ?_⟩ <;>
    simp only [srcR, sp, L, ctxR, stkR, dR, dp, cx, stackArg_wr, State.withRegions_gpr, hb.arg1, hb.r11, hb.r9,
      hb.r8, hb.rsp, below, sub24'] at *
  · exact (s.gpr .r9).isLt
  · exact hs.o_s
  · exact hs.s_w.symm
  · exact TPre.stk0 hs.b_s (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    simp
  · exact hs.s_d.symm

/-! ## The regions, within the frame's -/

omit hs in
/-- A part of the frame's words. -/
theorem in_frame {d n : Nat} (h : 24 ≤ d) (h' : d + n ≤ 48) :
    Covers [⟨fB s + BitVec.ofNat 64 d, n⟩] (u.rd ++ u.wr) :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨fB s + BitVec.ofNat 64 24, 24⟩, List.mem_append_right _ (by rw [hb.wr]; simp), d - 24,
      by simp only; rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h], by simp only; omega⟩

theorem rd_cov : Covers (rdB u ++ [srcR u]) (u.rd ++ u.wr) := by
  have eA := hb.addr 0
  have mem_rd : ∀ r ∈ s.rd, Covers [r] (u.rd ++ u.wr) := fun r h =>
    Covers.of_mem fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact List.mem_append_left _ (by rw [hb.rd]; exact h)
  refine Covers.cons (mem_rd _ ?_) (Covers.cons (mem_rd _ ?_) (Covers.cons (mem_rd _ ?_)
    (Covers.cons (mem_rd _ ?_) (Covers.cons ?_ (Covers.cons (mem_rd _ ?_) Covers.nil)))))
  · show (⟨u.gpr .rdi, 32⟩ : Region) ∈ _; rw [hb.rdi, hs.rd]; simp
  · show (⟨u.gpr .rsi, 12⟩ : Region) ∈ _; rw [hb.rsi, hs.rd]; simp
  · show (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region) ∈ _; rw [hb.rdx, hb.rcx, hs.rd]; simp
  · show (⟨stackArg u 0, 16⟩ : Region) ∈ _; rw [hb.arg0, hs.rd]; simp
  · show Covers [⟨stackArgAddr u 0, 16⟩] _
    rw [eA]; exact hb.in_frame (by decide) (by decide)
  · show (⟨u.gpr .r11, (u.gpr .r9).toNat⟩ : Region) ∈ _; rw [hb.r11, hb.r9, hs.rd]; simp

theorem wr_cov : Covers (wrB u) u.wr := by
  refine Covers.of_mem fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hb.wr, hs.wr]
  rcases hr with rfl | rfl
  · show (⟨u.gpr .r8, (u.gpr .r9).toNat⟩ : Region) ∈ _; rw [hb.r8, hb.r9, hs.dl]; simp
  · show (⟨stackArg u 1, 1696⟩ : Region) ∈ _; rw [hb.arg1]; simp

omit hs in
/-- The memory of the frame's state, apart from the frame. -/
theorem bytes_eq {p : Addr} {n : Nat} (hk : (estkR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt u.mem p n = bytesAt s.mem p n :=
  bytesAt_frame hb.mem (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (TPre.stk_disj hk (d := 24) (n := 24) (by decide)).symm) hn

end Body

/-! ## The function -/

/-- `framed c`, for verified code `c` that writes `rsp` only in its frames'
pushes and pops and uses at most 24 bytes of stack below `rsp`, run from
`open_to`'s entry state in the frame with its permissions narrowed to
`open`'s regions and the ciphertext's. -/
theorem framed_ok {c : Prog isa}
    (hv : ∀ s, sharedK.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ sharedK.post s s')
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ 24) {s : State} (hs : TPre s) :
    WP isa (framed c) s fun z => abiPreserved s z ∧ toPost s z := by
  refine WP.seq (WP.mono (toArgs_ok hs) fun h hh => ?_)
  have hsp' : h.gpr .rsp = s.gpr .rsp := hh.keep _ (by decide) (by decide) (by decide) (by decide)
  have hB := hs.fB_lt
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp']; have := hs.sp_lo; simp; omega
  have hu := body_of hs hh
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.inlineF hv hsp (by omega) (hu.spre hs) (Covers.append_left (hu.rd_cov hs) (hu.wr_cov hs).right)
    (hu.wr_cov hs) fun s₂ rd₂ wr₂ ab₂ f₂ _ post₂ => ?_
  have rsp₂ : s₂.gpr .rsp = (pushed frameRegs h).gpr .rsp := ab₂.1 _ calleeSaved_rsp
  refine ⟨rsp₂, wr₂, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      rw [popped_rsp, rsp₂, hu.rsp, Offset.add_ofNat_add_ofNat, TPre.rsp_eq]
      rfl
    · have hra : r ≠ .r10 := by rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' hra, ab₂.1 r hr, hu.cs r hr hr']
  · -- The return address: apart from what the shared code writes, and the frame.
    have hf := Frame.below_mono f₂ hd (by decide)
    rw [popped_mem]
    have e₁ : wrB (pushed frameRegs h) = [edR s, ewR s] := by
      show [(⟨(pushed frameRegs h).gpr .r8, ((pushed frameRegs h).gpr .r9).toNat⟩ : Region),
        ⟨stackArg (pushed frameRegs h) 1, 1696⟩] = _
      rw [hu.r8, hu.r9, hu.arg1]
    rw [e₁, hu.rsp] at hf
    simp only [below, sub24'] at hf
    rw [hf.readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl) | rfl
        · exact hs.r_d
        · exact hs.r_w
        · have := hs.ret_stk (d := 0) (n := 24) (by decide)
          rwa [BitVec.add_zero] at this) (by decide),
      hu.mem.readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hs.ret_stk (d := 24) (n := 24) (by decide)) (by decide)]
  · rw [popped_mxcsr, ab₂.2.2, hu.mx]
  · -- The postcondition, from the shared code's.
    have post' : openSPost ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h)))
        (s₂.withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) := post₂
    have eK : K ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) =
        bytesAt s.mem (s.gpr .rdi) 32 := by
      show bytesAt (pushed frameRegs h).mem ((pushed frameRegs h).gpr .rdi) 32 = _
      rw [hu.rdi]; exact hu.bytes_eq hs.b_k (by decide)
    have eN : N ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) =
        bytesAt s.mem (s.gpr .rsi) 12 := by
      show bytesAt (pushed frameRegs h).mem ((pushed frameRegs h).gpr .rsi) 12 = _
      rw [hu.rsi]; exact hu.bytes_eq hs.b_n (by decide)
    have eA : A ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) =
        bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat := by
      show bytesAt (pushed frameRegs h).mem ((pushed frameRegs h).gpr .rdx)
        ((pushed frameRegs h).gpr .rcx).toNat = _
      rw [hu.rdx, hu.rcx]; exact hu.bytes_eq hs.b_a (Nat.le_of_lt (s.gpr .rcx).isLt)
    have eC : C ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) =
        bytesAt s.mem (eSrc s) (eLn s) := by
      show bytesAt (pushed frameRegs h).mem ((pushed frameRegs h).gpr .r11)
        ((pushed frameRegs h).gpr .r9).toNat = _
      rw [hu.r11, hu.r9]; exact hu.bytes_eq hs.b_s (Nat.le_of_lt (s.gpr .r9).isLt)
    have eT : T0 ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) =
        bytesAt s.mem (eTg s) 16 := by
      show bytesAt (pushed frameRegs h).mem (stackArg (pushed frameRegs h) 0) 16 = _
      rw [hu.arg0]; exact hu.bytes_eq hs.b_t (by decide)
    have eD : dp ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) = eDst s := hu.r8
    have eL : L ((pushed frameRegs h).withRegions (rdB (pushed frameRegs h) ++ [srcR (pushed frameRegs h)]) (wrB (pushed frameRegs h))) = eLn s := by
      show ((pushed frameRegs h).gpr .r9).toNat = _; rw [hu.r9]
    have eR : (popped .r10 frameRegs.length s₂).gpr .rax = s₂.gpr .rax :=
      popped_gpr _ _ _ (by decide) (by decide)
    unfold openSPost at post'
    unfold toPost
    rw [eK, eN, eA, eC, eT, eD, eL] at post'
    rw [eR, popped_mem]
    exact post'

/-! ## Constant time -/

section
variable {σ₁ σ₂ : State} (p₁ : TPre σ₁) (p₂ : TPre σ₂) (hq : toPub σ₁ σ₂)
include p₁ p₂ hq

/-- The public data of the shared code's narrowed entry state, in two runs. -/
theorem body_pub {u₁ u₂ : State} (hu₁ : Body σ₁ u₁) (hu₂ : Body σ₂ u₂) :
    sharedPub (u₁.withRegions (rdB u₁ ++ [srcR u₁]) (wrB u₁)) (u₂.withRegions (rdB u₂ ++ [srcR u₂]) (wrB u₂)) := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, ql⟩ := hq
  have hB : fB σ₁ = fB σ₂ := by simp only [fB, qsp]
  refine ⟨⟨by show u₁.gpr .rdi = u₂.gpr .rdi; rw [hu₁.rdi, hu₂.rdi, q₁],
    by show u₁.gpr .rsi = u₂.gpr .rsi; rw [hu₁.rsi, hu₂.rsi, q₂],
    by show u₁.gpr .rdx = u₂.gpr .rdx; rw [hu₁.rdx, hu₂.rdx, q₃],
    by show u₁.gpr .rcx = u₂.gpr .rcx; rw [hu₁.rcx, hu₂.rcx, q₄],
    by show u₁.gpr .r8 = u₂.gpr .r8; rw [hu₁.r8, hu₂.r8, eDst, eDst, a₀],
    by show u₁.gpr .r9 = u₂.gpr .r9; rw [hu₁.r9, hu₂.r9, q₆],
    by show u₁.gpr .rsp = u₂.gpr .rsp; rw [hu₁.rsp, hu₂.rsp, hB],
    by show stackArg u₁ 0 = stackArg u₂ 0; rw [hu₁.arg0, hu₂.arg0, eTg, eTg, a₂],
    by show stackArg u₁ 1 = stackArg u₂ 1; rw [hu₁.arg1, hu₂.arg1, eW, eW, a₃]⟩,
    by show u₁.gpr .r11 = u₂.gpr .r11; rw [hu₁.r11, hu₂.r11, eSrc, eSrc, q₅], ?_⟩
  have leak : ∀ {σ u : State}, TPre σ → Body σ u →
      openSLeak (u.withRegions (rdB u ++ [srcR u]) (wrB u)) = toLeak σ := fun {σ u} hσ hu => by
    have eK : bytesAt u.mem (u.gpr .rdi) 32 = bytesAt σ.mem (σ.gpr .rdi) 32 := by
      rw [hu.rdi]; exact hu.bytes_eq hσ.b_k (by decide)
    have eN : bytesAt u.mem (u.gpr .rsi) 12 = bytesAt σ.mem (σ.gpr .rsi) 12 := by
      rw [hu.rsi]; exact hu.bytes_eq hσ.b_n (by decide)
    have eA : bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat = bytesAt σ.mem (σ.gpr .rdx) (σ.gpr .rcx).toNat := by
      rw [hu.rdx, hu.rcx]; exact hu.bytes_eq hσ.b_a (Nat.le_of_lt (σ.gpr .rcx).isLt)
    have eC : bytesAt u.mem (u.gpr .r11) (u.gpr .r9).toNat = bytesAt σ.mem (eSrc σ) (eLn σ) := by
      rw [hu.r11, hu.r9]; exact hu.bytes_eq hσ.b_s (Nat.le_of_lt (σ.gpr .r9).isLt)
    have eT : bytesAt u.mem (stackArg u 0) 16 = bytesAt σ.mem (eTg σ) 16 := by
      rw [hu.arg0]; exact hu.bytes_eq hσ.b_t (by decide)
    show [if (Spec.ChaCha20Poly1305.decrypt (bytesAt u.mem (u.gpr .rdi) 32) (bytesAt u.mem (u.gpr .rsi) 12)
      (bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat) (bytesAt u.mem (u.gpr .r11) (u.gpr .r9).toNat)
      (bytesAt u.mem (stackArg u 0) 16)).isSome then 1 else 0] = _
    rw [eK, eN, eA, eC, eT]; rfl
  rw [leak p₁ hu₁, leak p₂ hu₂, ql]

/-- The frame around code that is constant time from the shared code's
entry state, narrowed. -/
theorem framed_rel {c : Prog isa}
    (hv : ∀ s, sharedK.pre s → ∃ t s', Exec isa c s t s' ∧ sharedK.post s s')
    (hct : ConstantTime isa sharedK.pre sharedK.pub c) :
    RelCT isa (Eq2 σ₁ σ₂) (framed c) TT := by
  have qsp := hq.2.2.2.2.2.2.1
  refine rel_seq (rel_regs [.rsp] (by simp [qsp]) ⟨_, by taint_decide⟩) (toArgs_ok p₁) (toArgs_ok p₂)
    fun h₁ h₂ hh₁ hh₂ => ?_
  have hsp : ∀ {σ h}, Loaded σ h → h.gpr .rsp = σ.gpr .rsp := fun hh =>
    hh.keep _ (by decide) (by decide) (by decide) (by decide)
  refine rel_frame (by rw [hsp hh₁, hsp hh₂, qsp]) ?_
  have hu₁ := body_of p₁ hh₁
  have hu₂ := body_of p₂ hh₂
  refine (regionModel.relCT_inline (c := c) (Pre := sharedK.pre) (Pub := sharedK.pub) hv hct
    (P := Eq2 (pushed frameRegs h₁) (pushed frameRegs h₂)) fun x₁ x₂ ⟨e₁, e₂⟩ => ?_).mono
    (fun _ _ h => h) fun _ _ h => h
  subst e₁ e₂
  exact ⟨_, _, _, _, hu₁.spre p₁, hu₂.spre p₂, body_pub p₁ p₂ hq hu₁ hu₂,
    Covers.append_left (hu₁.rd_cov p₁) (hu₁.wr_cov p₁).right, hu₁.wr_cov p₁,
    Covers.append_left (hu₂.rd_cov p₂) (hu₂.wr_cov p₂).right, hu₂.wr_cov p₂⟩

end

/-! ## The body of an instance -/

/-- The shared code the body of the instance calling the implementation `v`
of `vg_chacha20_xor` runs in the frame. -/
abbrev inner (v : XorImpl) : Prog isa :=
  if v.poly = .avx2 then Stitch.openStitchedShared v.callee .avx2 else openShared v.callee v.poly

theorem inner_ok (v : XorImpl) (s : State) (hs : sharedK.pre s) :
    ∃ t s', Exec isa (inner v) s t s' ∧ abiPreserved s s' ∧ sharedK.post s s' := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.stitchedShared_ok v hv s hs
    rw [hv] at h
    simpa only [inner, hv, ↓reduceIte] using h
  · simpa only [inner, hv, ↓reduceIte] using shared_ok v s hs

theorem inner_ct (v : XorImpl) : ConstantTime isa sharedK.pre sharedK.pub (inner v) := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.stitchedShared_ct v hv
    rw [hv] at h
    simpa only [inner, hv, ↓reduceIte] using h
  · simpa only [inner, hv, ↓reduceIte] using shared_ct v

theorem inner_spSafe (v : XorImpl) : (inner v).all (fun i => !isa.writesSp i) = true := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.openS_spSafe v hv
    rw [hv] at h
    simp only [Stitch.openStitched, Code.all, Bool.and_eq_true] at h
    simpa only [inner, hv, ↓reduceIte, Stitch.openStitchedShared, Code.all, Bool.and_eq_true] using h.2
  · have h := open_spSafe v
    simp only [«open», Code.all, Bool.and_eq_true] at h
    simpa only [inner, hv, ↓reduceIte] using h.2

theorem inner_xdepth (v : XorImpl) : (inner v).x86_64Depth ≤ 24 := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.openS_xdepth v
    rw [hv] at h
    simp only [Stitch.openStitched, Code.x86_64Depth, Nat.max_le] at h
    simpa only [inner, hv, ↓reduceIte, Stitch.openStitchedShared, Code.x86_64Depth, Nat.max_le] using h.2
  · have h := open_xdepth v
    simp only [«open», Code.x86_64Depth, Nat.max_le] at h
    simpa only [inner, hv, ↓reduceIte] using h.2

theorem body_eq (v : XorImpl) : body v.callee v.poly = framed (inner v) := rfl

theorem body_spSafe (v : XorImpl) : (body v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  rw [body_eq]
  simp only [framed, Code.all, inner_spSafe v, Bool.and_true]
  decide

theorem body_xdepth (v : XorImpl) : (body v.callee v.poly).x86_64Depth ≤ 48 := by
  have h := inner_xdepth v
  rw [body_eq]
  simp only [framed, Code.x86_64Depth, X86_64.Instr.frameBytes, Nat.zero_max]
  change _ + 24 ≤ 48
  omega

theorem body_correct (v : XorImpl) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa (body v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ toK.post s s' :=
  let ⟨t, s', e, a, p⟩ := framed_ok (inner_ok v) (SpSafe.of_all (inner_spSafe v)) (inner_xdepth v) hs
  ⟨t, s', e, a, p⟩

theorem body_ct (v : XorImpl) : ConstantTime isa toK.pre toK.pub (body v.callee v.poly) :=
  ct_of fun _ _ p₁ p₂ hq => framed_rel p₁ p₂ hq
    (fun s hs => let ⟨t, s', e, _, p⟩ := inner_ok v s hs; ⟨t, s', e, p⟩) (inner_ct v)

/-! ## The contract -/

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem tpre_of_spec {s : State} (h : (openToScratchContract X86_64.abi 212 48).pre s) : TPre s := by
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

theorem pub_of {s₁ s₂ : State} (hp : (openToScratchContract X86_64.abi 212 48).pub s₁ s₂) : toPub s₁ s₂ := by
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

theorem toSat_pre : ∃ s, (openToScratchContract X86_64.abi 212 48).pre s := by
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
theorem to_implies : toK.Implies (openToScratchContract X86_64.abi 212 48) where
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
    Verified X86_64.target (body v.callee v.poly) (openToScratchContract X86_64.abi 212 48) :=
  Verified.of_correct (k := toK) (body_correct v) (body_ct v) to_implies

/-! ## The frame of `work` -/

/-- A state satisfying the precondition, without the working space. -/
def toFrameSat : State :=
  { toSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩, ⟨0x8008, 24⟩],
               wr := [⟨0x3000, 0⟩] }

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem toFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792).pre s := by
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
      (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792) :=
  X86_64.Verified.stackArgScratchWipedXPre (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 212) (pre := Spec.ChaCha20Poly1305.openToPre X86_64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost X86_64.abi.ptrBits) (wa := true) (stack := 48)
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

theorem pub_len {s t : State} (h : (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792).pub s t) :
    s.gpr .r9 = t.gpr .r9 := by
  rw [Spec.ChaCha20Poly1305.openToContract, pubL_args (by decide)] at h
  have hh := h.2.1 5 (by decide)
  change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
  simpa only [BitVec.setWidth_eq] using hh

/-- A public length choice between two framed implementations. -/
theorem choose {b : List Instr} {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified X86_64.target a (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792))
    (hc : Verified X86_64.target c (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792))
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified X86_64.target (.seq (.block b) (Code.iteCold .b a c))
      (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792) :=
  Shared.chooseK
    (fun _ _ hf hs => Shared.flags_pre_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1792) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hs)
    (fun _ _ _ hf hP => Shared.flags_post_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1792) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hP)
    (fun _ _ _ _ hf hg hp => Shared.flags_pub_sig (sig := Spec.ChaCha20Poly1305.openToSig)
      (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
      (stack := 1792) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hg hp)
    (fun _ _ hp => pub_len hp) toFrameSat_pre ha hc hb ht

/-- `vg_chacha20_poly1305_open_to` of the instance calling the
implementation `v` of `vg_chacha20_xor`. -/
theorem openTo_verified (v : XorImpl) :
    Verified X86_64.target (openToCode v.callee v.poly) (Spec.ChaCha20Poly1305.openToContract X86_64.abi 1792) := by
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
