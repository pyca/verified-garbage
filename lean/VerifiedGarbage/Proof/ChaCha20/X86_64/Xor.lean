module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
public import VerifiedGarbage.Proof.ChaCha20.Keystream
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
meta import VerifiedGarbage.Proof.ChaCha20.Keystream
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20 keystream XOR on x86-64

The contracts of `vg_chacha20_xor` (`xorTo`: from a source to a destination;
`xorIn`: in place), how a proof of the one gives the other (`okIn_of_okTo`,
`ctIn_of_ctTo`), and in-place calls (`wpCallIn`, `relCallIn`); then the
proof of the baseline implementation (`Impl.ChaCha20.X86_64.Xor`).

The source and the destination are either the same buffer or apart
(`XPre.alias`): the loop's invariant says what the destination holds before
the bytes done (`OInv.data`), and the source after them is intact (`src_of`)
in both cases.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8,
len: usize, buf: *mut [u32; 80])`: XORs the first `len` bytes of the keystream
of the state at `state` into the `len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, the return address on the stack, or the 8
bytes below it, where the call of the block function stores its return
address; `data` does not wrap around the end of the address space. The
pointers and the length are public; the state and the data are secret. -/
def xorX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `xorX86_64` with `k` bytes of stack below the return address, for an
implementation whose calls use them, and that returns with `rsi` pointing at
`buf` (for a caller that recomputes pointers from it): what callers of any
implementation of `vg_chacha20_xor` rely on (see `Variant.lean`). -/
def xorStack (k : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx
  pub := xorX86_64.pub

theorem xorStack_pre8 : (xorStack 8).pre = xorX86_64.pre := rfl

/-- The contract of every implementation of `vg_chacha20_xor(state = rdi,
src = rsi, len = rdx, buf = rcx, dst = r8)`, with `k` bytes of stack below
the return address for its calls: writes the `len` bytes at `src` XORed with
the first `len` bytes of the keystream of the state at `state` to the `len`
bytes at `dst`, and returns with `rsi` pointing at `buf`.

The code may read `src` (`len` bytes), and read and write `state` (64 bytes;
its contents on exit are unspecified), `dst` (`len` bytes) and `buf` (320
bytes of working space). `dst` is either `src` (in place) or apart from it;
otherwise these may not overlap each other; the buffers but `src` may not
overlap the return address, and none the `k` bytes of stack below it; `src`
and `dst` do not wrap around the end of the address space. The pointers and
the length are public; the state and the data are secret. -/
def xorTo (k : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let src : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let dst : Region := ⟨s.gpr .r8, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩
    s.rd = [src] ∧ s.wr = [state, dst, buf] ∧
    state.Disjoint src ∧ state.Disjoint dst ∧ state.Disjoint buf ∧ src.Disjoint buf ∧ dst.Disjoint buf ∧
    (s.gpr .r8 = s.gpr .rsi ∨ src.Disjoint dst) ∧
    ret.Disjoint state ∧ ret.Disjoint dst ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint src ∧ stack.Disjoint dst ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .r8) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat) ∧
    s'.gpr .rsi = s.gpr .rcx
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `xorStack` with `r8` (the destination) at `rsi`: an implementation
called in place. -/
def xorIn (k : Nat) : Contract X86_64.isa where
  pre s := (xorStack k).pre s ∧ s.gpr .r8 = s.gpr .rsi
  post := (xorStack k).post
  pub := (xorStack k).pub

section
open VG.X86_64

/-- An in-place call's state, narrowed to read the data too: `xorTo`'s
precondition. -/
theorem xorTo_of_in {k : Nat} {s : X86_64.State} (h : (xorIn k).pre s) :
    (xorTo k).pre (s.withRegions [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩] s.wr) := by
  obtain ⟨⟨hrd, hwr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h8r⟩ := h
  simp only [xorTo, X86_64.State.withRegions_gpr, X86_64.State.withRegions_rd, X86_64.State.withRegions_wr, h8r, hwr]
  exact ⟨trivial, trivial, h1, h1, h2, h3, h3, .inl trivial, h4, h5, h6, h7, h8, h8, h9, h10, h10⟩

theorem xorIn_covers {k : Nat} {s : X86_64.State} (h : (xorIn k).pre s) :
    Covers ([⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩] ++ s.wr) (s.rd ++ s.wr) := by
  obtain ⟨⟨-, hwr, -⟩, -⟩ := h
  exact Covers.of_mem fun r hr => List.mem_append_right _ (by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; rw [hwr]; simp
    · exact hr)

/-- An implementation correct for `xorTo` is correct called in place. -/
theorem okIn_of_okTo {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorTo k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorTo k).post s s') :
    ∀ s, (xorIn k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorIn k).post s s' := by
  intro s hs
  obtain ⟨t, s₁, he, ha, hp, hrsi⟩ := hv _ (xorTo_of_in hs)
  obtain ⟨he', e⟩ := regionModel.inline he (xorIn_covers hs) (Covers.refl _)
  refine ⟨t, _, he', ha, ?_, hrsi⟩
  have h8 := hs.2
  simp only [X86_64.State.withRegions_gpr, X86_64.State.withRegions_mem, h8] at hp
  rw [← e] at hp
  exact hp

/-- An implementation constant time for `xorTo` is constant time called in
place. -/
theorem ctIn_of_ctTo {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorTo k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorTo k).post s s')
    (hct : ConstantTime isa (xorTo k).pre (xorTo k).pub c) :
    ConstantTime isa (xorIn k).pre (xorIn k).pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨u₁, f₁⟩ := regionModel.trace_narrow (fun s h => let ⟨t, s', e, _, _⟩ := hv s h; ⟨t, s', e, trivial⟩)
    (xorTo_of_in h₁) (xorIn_covers h₁) (Covers.refl _) e₁
  obtain ⟨u₂, f₂⟩ := regionModel.trace_narrow (fun s h => let ⟨t, s', e, _, _⟩ := hv s h; ⟨t, s', e, trivial⟩)
    (xorTo_of_in h₂) (xorIn_covers h₂) (Covers.refl _) e₂
  refine hct _ _ _ _ _ _ (xorTo_of_in h₁) (xorTo_of_in h₂) ?_ f₁ f₂
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  simp only [xorTo, X86_64.State.withRegions_gpr, h₁.2, h₂.2]
  exact ⟨p1, p2, p3, p4, p2, p5⟩


/-! ## In-place calls

`Impl.ChaCha20.X86_64.Xor.callIn n c` sets `r8` (the destination) to `rsi`
(the source), then calls `c`: from a caller that establishes `xorStack`'s
precondition, as for a call of code proven in place. -/

theorem mov_r8 (s : X86_64.State) :
    execBlock isa [.mov .r8 (.reg .rsi)] s = some (s.setReg .r8 (s.gpr .rsi), []) := rfl

/-- The state a call starts in, after `r8` is set, agrees with the one before
on everything but `r8`. -/
theorem entry_r8 (s : X86_64.State) (x : BitVec 64) (rd wr : List Region) {r : Reg} (hr : r ≠ .r8) :
    ((s.setReg .r8 x).callEntry.withRegions rd wr).gpr r = (s.callEntry.withRegions rd wr).gpr r := by
  by_cases hsp : r = .rsp
  · subst hsp; simp only [X86_64.State.withRegions_gpr, X86_64.State.callEntry_rsp, RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8)]
  · simp only [X86_64.State.withRegions_gpr, X86_64.State.callEntry_gpr _ hsp, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem entry_r8_mem (s : X86_64.State) (x : BitVec 64) (rd wr : List Region) :
    ((s.setReg .r8 x).callEntry.withRegions rd wr).mem = (s.callEntry.withRegions rd wr).mem := by
  simp only [X86_64.State.withRegions_mem, X86_64.State.callEntry_mem, RegUpd.mem_setReg,
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8)]; rfl

theorem entry_r8_self (s : X86_64.State) (rd wr : List Region) :
    ((s.setReg .r8 (s.gpr .rsi)).callEntry.withRegions rd wr).gpr .r8 =
      ((s.setReg .r8 (s.gpr .rsi)).callEntry.withRegions rd wr).gpr .rsi := by
  simp only [X86_64.State.withRegions_gpr, X86_64.State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    X86_64.State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsi = .r8)]

theorem xorStack_pre_r8 {k : Nat} {s : X86_64.State} {x : BitVec 64} {rd wr : List Region}
    (h : (xorStack k).pre (s.callEntry.withRegions rd wr)) :
    (xorStack k).pre ((s.setReg .r8 x).callEntry.withRegions rd wr) := by
  simp only [xorStack, X86_64.State.withRegions_rd, X86_64.State.withRegions_wr] at h ⊢
  rw [entry_r8 s x rd wr (by decide : Reg.rdi ≠ .r8), entry_r8 s x rd wr (by decide : Reg.rsi ≠ .r8),
    entry_r8 s x rd wr (by decide : Reg.rdx ≠ .r8), entry_r8 s x rd wr (by decide : Reg.rcx ≠ .r8),
    entry_r8 s x rd wr (by decide : Reg.rsp ≠ .r8)]
  exact h

theorem xorStack_post_r8 {k : Nat} {s s₂ : X86_64.State} {x : BitVec 64} {rd wr : List Region}
    (h : (xorStack k).post ((s.setReg .r8 x).callEntry.withRegions rd wr) s₂) :
    (xorStack k).post (s.callEntry.withRegions rd wr) s₂ := by
  simp only [xorStack, xorX86_64] at h ⊢
  rwa [entry_r8 s x rd wr (by decide : Reg.rdi ≠ .r8), entry_r8 s x rd wr (by decide : Reg.rsi ≠ .r8),
    entry_r8 s x rd wr (by decide : Reg.rdx ≠ .r8), entry_r8 s x rd wr (by decide : Reg.rcx ≠ .r8),
    entry_r8_mem] at h

theorem xorStack_pub_r8 {k : Nat} {s₁ s₂ : X86_64.State} {x₁ x₂ : BitVec 64} {rd₁ wr₁ rd₂ wr₂ : List Region}
    (h : (xorStack k).pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂)) :
    (xorStack k).pub ((s₁.setReg .r8 x₁).callEntry.withRegions rd₁ wr₁)
      ((s₂.setReg .r8 x₂).callEntry.withRegions rd₂ wr₂) := by
  simp only [xorStack, xorX86_64] at h ⊢
  rwa [entry_r8 s₁ x₁ rd₁ wr₁ (by decide : Reg.rdi ≠ .r8), entry_r8 s₁ x₁ rd₁ wr₁ (by decide : Reg.rsi ≠ .r8),
    entry_r8 s₁ x₁ rd₁ wr₁ (by decide : Reg.rdx ≠ .r8), entry_r8 s₁ x₁ rd₁ wr₁ (by decide : Reg.rcx ≠ .r8),
    entry_r8 s₁ x₁ rd₁ wr₁ (by decide : Reg.rsp ≠ .r8),
    entry_r8 s₂ x₂ rd₂ wr₂ (by decide : Reg.rdi ≠ .r8), entry_r8 s₂ x₂ rd₂ wr₂ (by decide : Reg.rsi ≠ .r8),
    entry_r8 s₂ x₂ rd₂ wr₂ (by decide : Reg.rdx ≠ .r8), entry_r8 s₂ x₂ rd₂ wr₂ (by decide : Reg.rcx ≠ .r8),
    entry_r8 s₂ x₂ rd₂ wr₂ (by decide : Reg.rsp ≠ .r8)]

/-- An in-place call of code proven for `xorIn k`: as `WP.call` with
`xorStack k`. -/
theorem wpCallIn {n : String} {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorIn k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorIn k).post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : X86_64.State} {rd wr : List Region}
    (hpre : (xorStack k).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : X86_64.State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs (Impl.ChaCha20.X86_64.Xor.callIn n c), Taint.clobbers i r = false) →
        s'.gpr r = s.gpr r) →
      (∃ s₂ : X86_64.State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xorStack k).post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (Impl.ChaCha20.X86_64.Xor.callIn n c) s Q := by
  refine WP.seq (WP.block ⟨_, mov_r8 s, ?_⟩)
  refine WP.call (k := xorIn k) hv hsp hd ⟨xorStack_pre_r8 hpre, entry_r8_self s rd wr⟩ hc hw ?_
  intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hpost⟩
  have hsp' : (s.setReg .r8 (s.gpr .rsi)).gpr .rsp = s.gpr .rsp :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine hQ s' hrd hwr (fun r hr => ?_) (by rw [hsp'] at hf; exact hf) (fun r hr => ?_)
    ⟨s₂, hm₂, hg₂, xorStack_post_r8 hpost⟩
  · have hr8 : r ≠ .r8 := by intro h; subst h; simp [calleeSaved] at hr
    rw [hcs r hr, RegUpd.gpr_setReg_of_ne _ _ hr8]
  · have h8 : r ≠ .r8 := by
      intro h; subst h
      have := hr (.mov .r8 (.reg .rsi)) (by simp [instrs])
      exact absurd this (by decide)
    rw [hkeep r fun i hi => hr i (by
        simp only [instrs, List.mem_append]; exact .inr hi),
      RegUpd.gpr_setReg_of_ne _ _ h8]

/-- Two runs of an in-place call of code proven for `xorIn k`, with
`xorStack k`'s public arguments agreeing: as `RelCT.callEx`. -/
theorem relCallIn {n : String} {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorIn k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorIn k).post s s')
    (hct : ConstantTime isa (xorIn k).pre (xorIn k).pub c) {P : X86_64.State → X86_64.State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (xorStack k).pre (s₁.callEntry.withRegions rd₁ wr₁) ∧
      (xorStack k).pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      (xorStack k).pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (Impl.ChaCha20.X86_64.Xor.callIn n c) fun _ _ => True := by
  refine RelCT.seq (R := fun x y => ∃ a b, P a b ∧ x = a.setReg .r8 (a.gpr .rsi) ∧
    y = b.setReg .r8 (b.gpr .rsi)) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    rw [Exec.block_iff, mov_r8, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁
    obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, _, _, hp, rfl, rfl⟩
  · refine RelCT.callEx hv hct fun x y ⟨a, b, hab, ex, ey⟩ => ?_
    subst ex ey
    obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP a b hab
    exact ⟨rd₁, wr₁, rd₂, wr₂, ⟨xorStack_pre_r8 p₁, entry_r8_self a rd₁ wr₁⟩,
      ⟨xorStack_pre_r8 p₂, entry_r8_self b rd₂ wr₂⟩, xorStack_pub_r8 hpub, c₁, w₁, c₂, w₂,
      by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8),
        RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8), hsp]⟩

/-! ## Calls from a source to a destination

`Impl.ChaCha20.X86_64.Xor.callTo n c` sets `r8` (the destination) to
`rsi + r11`, then calls `c`, proven for `xorTo k`: from a caller that
establishes `xorTo k`'s precondition for the state with `r8` set
(`toR8`), which the state after the `add` is but for the flags. -/

/-- The state with `r8` at `rsi + r11`. -/
abbrev toR8 (s : X86_64.State) : X86_64.State := s.setReg .r8 (s.gpr .r11 + s.gpr .rsi)

theorem to_r8 (s : X86_64.State) : ∃ s₁, execBlock isa [.mov .r8 (.reg .r11), .alu .add .r8 (.reg .rsi)] s =
    some (s₁, []) ∧ s₁.gpr = (toR8 s).gpr ∧ s₁.mem = (toR8 s).mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
    s₁.unknowns = (toR8 s).unknowns := by
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl⟩
  funext r
  by_cases h : r = .r8
  · subst h; simp only [RegUpd.gpr_setReg_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags]

/-- States that agree on the registers, memory and unknowns enter a call
alike. -/
theorem entry_congr {s₁ t : X86_64.State} (hg : s₁.gpr = t.gpr) (hm : s₁.mem = t.mem)
    (hu : s₁.unknowns = t.unknowns) (rd wr : List Region) :
    (s₁.callEntry.withRegions rd wr).gpr = (t.callEntry.withRegions rd wr).gpr ∧
    (s₁.callEntry.withRegions rd wr).mem = (t.callEntry.withRegions rd wr).mem := by
  simp only [X86_64.State.withRegions, X86_64.State.callEntry, X86_64.State.setReg, hg, hm, hu]
  exact ⟨trivial, trivial⟩

theorem xorTo_pre_congr {k : Nat} {t t' : X86_64.State} (hg : t'.gpr = t.gpr) (hr : t'.rd = t.rd)
    (hw : t'.wr = t.wr) (h : (xorTo k).pre t) : (xorTo k).pre t' := by
  simp only [xorTo] at h ⊢; rw [hg, hr, hw]; exact h

theorem xorTo_post_congr {k : Nat} {t t' s₂ : X86_64.State} (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem)
    (h : (xorTo k).post t s₂) : (xorTo k).post t' s₂ := by
  simp only [xorTo] at h ⊢; rw [hg, hm]; exact h

theorem xorTo_pub_congr {k : Nat} {t₁ t₁' t₂ t₂' : X86_64.State} (hg₁ : t₁'.gpr = t₁.gpr) (hg₂ : t₂'.gpr = t₂.gpr)
    (h : (xorTo k).pub t₁ t₂) : (xorTo k).pub t₁' t₂' := by
  simp only [xorTo] at h ⊢; rw [hg₁, hg₂]; exact h

/-- A call from a source to a destination of code proven for `xorTo k`: as
`WP.call`, for the state with `r8` set. -/
theorem wpCallTo {n : String} {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorTo k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorTo k).post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : X86_64.State} {rd wr : List Region}
    (hpre : (xorTo k).pre ((toR8 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : X86_64.State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs (Impl.ChaCha20.X86_64.Xor.callTo n c), Taint.clobbers i r = false) →
        s'.gpr r = s.gpr r) →
      (∃ s₂ : X86_64.State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xorTo k).post ((toR8 s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (Impl.ChaCha20.X86_64.Xor.callTo n c) s Q := by
  obtain ⟨s₁, e, hg, hm, hr, hw', hu⟩ := to_r8 s
  have ⟨eg, em⟩ := entry_congr hg hm hu rd wr
  have hg1 : ∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r := fun r h => by
    rw [hg, RegUpd.gpr_setReg_of_ne _ _ h]
  have hm1 : s₁.mem = s.mem := by rw [hm, RegUpd.mem_setReg]
  refine WP.seq (WP.block ⟨_, e, ?_⟩)
  refine WP.call hv hsp hd (xorTo_pre_congr eg (by simp) (by simp) hpre)
    (by rw [hr, hw']; exact hc) (by rw [hw']; exact hw) ?_
  intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hpost⟩
  have hsp' : s₁.gpr .rsp = s.gpr .rsp := hg1 _ (by decide)
  refine hQ s' (by rw [hrd, hr]) (by rw [hwr, hw']) (fun r hr' => ?_) (by rw [hsp', hm1] at hf; exact hf)
    (fun r hr' => ?_) ⟨s₂, hm₂, hg₂, xorTo_post_congr eg.symm em.symm hpost⟩
  · have hr8 : r ≠ .r8 := by intro h; subst h; simp [calleeSaved] at hr'
    rw [hcs r hr', hg1 r hr8]
  · have h8 : r ≠ .r8 := by
      intro h; subst h
      have := hr' (.mov .r8 (.reg .r11)) (by simp [instrs])
      exact absurd this (by decide)
    rw [hkeep r fun i hi => hr' i (by
        simp only [instrs, List.mem_append]; exact .inr hi), hg1 r h8]

/-- Two runs of a call from a source to a destination of code proven for
`xorTo k`: as `RelCT.callEx`, for the states with `r8` set. -/
theorem relCallTo {n : String} {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorTo k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorTo k).post s s')
    (hct : ConstantTime isa (xorTo k).pre (xorTo k).pub c) {P : X86_64.State → X86_64.State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (xorTo k).pre ((toR8 s₁).callEntry.withRegions rd₁ wr₁) ∧
      (xorTo k).pre ((toR8 s₂).callEntry.withRegions rd₂ wr₂) ∧
      (xorTo k).pub ((toR8 s₁).callEntry.withRegions rd₁ wr₁) ((toR8 s₂).callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (Impl.ChaCha20.X86_64.Xor.callTo n c) fun _ _ => True := by
  refine RelCT.seq (R := fun (x y : X86_64.State) => ∃ a b, P a b ∧ x.gpr = (toR8 a).gpr ∧ x.mem = (toR8 a).mem ∧
    x.rd = a.rd ∧ x.wr = a.wr ∧ x.unknowns = (toR8 a).unknowns ∧ y.gpr = (toR8 b).gpr ∧
    y.mem = (toR8 b).mem ∧ y.rd = b.rd ∧ y.wr = b.wr ∧ y.unknowns = (toR8 b).unknowns) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨x, ex, gx, mx, rx, wx, ux⟩ := to_r8 s₁
    obtain ⟨y, ey, gy, my, ry, wy, uy⟩ := to_r8 s₂
    rw [Exec.block_iff, ex, Option.some.injEq, Prod.mk.injEq] at e₁
    rw [Exec.block_iff, ey, Option.some.injEq, Prod.mk.injEq] at e₂
    obtain ⟨rfl, rfl⟩ := e₁
    obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, _, _, hp, gx, mx, rx, wx, ux, gy, my, ry, wy, uy⟩
  · refine RelCT.callEx hv hct fun x y ⟨a, b, hab, gx, mx, rx, wx, ux, gy, my, ry, wy, uy⟩ => ?_
    obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP a b hab
    have ex := (entry_congr gx mx ux rd₁ wr₁).1
    have ey := (entry_congr gy my uy rd₂ wr₂).1
    refine ⟨rd₁, wr₁, rd₂, wr₂, xorTo_pre_congr ex rfl rfl p₁, xorTo_pre_congr ey rfl rfl p₂,
      xorTo_pub_congr ex ey hpub, by rw [rx, wx]; exact c₁, by rw [wx]; exact w₁, by rw [ry, wy]; exact c₂,
      by rw [wy]; exact w₂, ?_⟩
    rw [gx, gy, RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8),
      RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsp = .r8), hsp]

end

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Xor

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Xor
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast readW_writeW_off
  block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
/-- The source. -/
abbrev sp : Addr := s₀.gpr .rsi
/-- The destination. -/
abbrev dp : Addr := s₀.gpr .r8
abbrev L : Nat := (s₀.gpr .rdx).toNat
abbrev bp : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev sR : Region := ⟨sp s₀, L s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stackR : Region := below (s₀.gpr .rsp) 8
/-- The state, the source, the destination and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev X0 (k : Nat) : Byte := s₀.mem (sp s₀ + BitVec.ofNat 64 k)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = [sR s₀]
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_s : (stR s₀).Disjoint (sR s₀)
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  s_b : (sR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  /-- In place, or apart. -/
  alias : dp s₀ = sp s₀ ∨ (sR s₀).Disjoint (dR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  stk_st : (stackR s₀).Disjoint (stR s₀)
  stk_s : (stackR s₀).Disjoint (sR s₀)
  stk_d : (stackR s₀).Disjoint (dR s₀)
  stk_b : (stackR s₀).Disjoint (bR s₀)
  nowrap_s : (sp s₀).toNat + L s₀ ≤ 2 ^ 64
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : (Proof.ChaCha20.xorTo 8).pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- Our caller's `rbx, rbp, r12, r13`, saved in `buf[256, 288)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (bp s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 288 := by decide

/-- The regions the code writes: its buffers and the return address of its calls. -/
abbrev frameR (s₀ : State) : List Region := [stR s₀, dR s₀, bR s₀, stackR s₀]

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = sp s₀ + BitVec.ofNat 64 (P s₀ j)
  r13 : s.gpr .r13 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rsi : s.gpr .rsi = bp s₀
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then X0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem

/-- The source after the first `p` bytes is intact, when the destination
holds the source from there on (in place) or is apart from it. -/
theorem src_of {s₀ : State} (hp : XPre s₀) {m : Mem} {p : Nat}
    (hd : ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) =
      if k < p then X0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k)
    (hf : Frame (frameR s₀) s₀.mem m) {k : Nat} (hpk : p ≤ k) (hk : k < L s₀) :
    m (sp s₀ + BitVec.ofNat 64 k) = X0 s₀ k := by
  rcases hp.alias with he | hdis
  · have := hd k hk
    rw [ite_eq_right (by omega)] at this
    simp only [X0, D0, dp, sp] at this he ⊢
    rw [← he]; exact this
  · exact hf.bytes (R := sR s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.st_s.symm
      · exact hdis
      · exact hp.s_b
      · exact hp.stk_s.symm) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk

/-! ## Memory -/

theorem XPre.w_b {s₀ : State} (hp : XPre s₀) : bR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (off p 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  have e : p + BitVec.ofNat 64 (4 * i) = off p (4 * i) := by rw [off, ofInt_natCast]
  rw [e]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (Or.inl rfl) (by lit_omega) (by lit_omega) (by lit_omega)

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := by
  have := contains_off (base := b) h hd
  rwa [ofInt_natCast] at this

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .r8), .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      OInv s₀ 0 s ∧ s.zf = some (decide (L s₀ = 0)) := by
  refine Spill.save_then .rcx saved (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    exact ⟨_, hp.w_b, Offset.contains_base _ (by omega) (by lit_omega)⟩
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, 
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hf : Frame [bR s₀] s₀.mem (Spill.saveMem s₀.mem (bp s₀) s₀.gpr saved) :=
    Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega) (by decide)
  refine ⟨⟨by simp, by simp [P], by simp [P],
    by simp [P], by simp, fun r hr => ?_, rfl,
    rfl, ?_, fun k hk => ?_, ?_, hf.mono (by simp)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk
  · exact Spill.saveMem_saved _ _ _ _ (by decide)
  · simp only [BitVec.and_self, L]
    by_cases h : (s₀.gpr .rdx).toNat = 0
    · simp [BitVec.eq_of_toNat_eq (x := s₀.gpr .rdx) (y := 0) h]
    · have : s₀.gpr .rdx ≠ 0 := fun h' => h (by simp [h'])
      simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨off (bp s₀) 256, 32⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := by
  simp only [savR, off, ofInt_natCast]
  exact Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := by
  simp only [savR, off, ofInt_natCast]
  exact Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp r hr => by
    have := saved_bound p hp
    refine (hd r hr).sub_left ?_
    simp only [savR, off, ofInt_natCast]
    exact Offset.sub _ (by omega) (by omega)

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.rsi, .rsp]

theorem block_keeps : ((instrs Impl.ChaCha20.X86_64.block).all fun i =>
    kept.all fun r => !Taint.clobbers i r) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs Impl.ChaCha20.X86_64.block, Taint.clobbers i r = false := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp block_keeps i hi) r hr
  simpa using this

theorem block_depth : Impl.ChaCha20.X86_64.block.depth = 0 := by lit_decide


theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by lit_omega)

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

set_option simprocs false in
theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdi (.reg .rbx)]) (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block))
      s (AInv s₀ j) := by
  have h₁ : WP isa (.block [.mov .rdi (.reg .rbx)]) s fun s₁ =>
      s₁.gpr .rdi = st s₀ ∧ (∀ r, r ≠ .rdi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp [State.setReg, h.rbx], fun r hr => by simp [State.setReg, hr], rfl, rfl, rfl⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [e₂ _ (by decide)]; exact h.keep .rsp (by simp)
  have hrsi : s₁.gpr .rsi = bp s₀ := by rw [e₂ _ (by decide)]; exact h.rsi
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hwr : s₁.wr = [stR s₀, dR s₀, bR s₀] := by rw [e₄, h.wr, hp.wr]
  have hrd : s₁.rd = [sR s₀] := by rw [e₃, h.rd, hp.rd]
  have hstk : below (s₁.gpr .rsp) 8 = stackR s₀ := by rw [hsp]
  refine WP.call (k := Proof.ChaCha20.blockX86_64) block_correct (block_keeps_reg (by simp [kept]))
    (by rw [block_depth]; decide) (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hsp]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm,
      hp.stk_b.sub_right (b256_sub s₀)⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ hcs hf hkeep ⟨s₃, hm₃, _, hpost⟩
    rw [block_depth, hstk] at hf
    have g : ∀ r ∈ calleeSaved, r ≠ .rdi → s₂.gpr r = s.gpr r := fun r hr hne => by
      rw [hcs r hr, e₂ r hne]
    have hd : ∀ R : Region, R.Disjoint (b256 s₀) → R.Disjoint (stackR s₀) →
        ∀ r ∈ [b256 s₀] ++ [stackR s₀], R.Disjoint r := by
      intro R h₁ h₂ r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption
    have hst : stateAt s₂.mem (st s₀) = stateAt s₁.mem (st s₀) :=
      stateAt_frame hf (hd _ (hp.st_b.sub_right (b256_sub s₀)) hp.stk_st.symm)
    refine ⟨⟨by rw [g .rbx (by simp [calleeSaved]) (by decide), h.rbx],
      by rw [g .rbp (by simp [calleeSaved]) (by decide), h.rbp],
      by rw [g .r13 (by simp [calleeSaved]) (by decide), h.r13],
      by rw [g .r12 (by simp [calleeSaved]) (by decide), h.r12],
      by rw [hkeep .rsi (block_keeps_reg (by simp [kept])), hrsi],
      fun r hr => ?_, by rw [hrd₂, e₃, h.rd], by rw [hwr₂, e₄, h.wr],
      by rw [hst, e₅, h.cnt], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
    · have hr' : r ∈ calleeSaved ∧ r ≠ .rdi := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp (config := {decide := true})
      rw [g r hr'.1 hr'.2]
      exact h.keep r hr
    · rw [hf.bytes (R := dR s₀) (hd _ (hp.d_b.sub_right (b256_sub s₀)) hp.stk_d.symm)
        (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk, e₅]
      exact h.data k hk
    · rw [e₅] at hf
      exact h.saved.frame hf (hd _ (savR_b256 s₀) (hp.stk_b.symm.sub_left (savR_sub s₀)))
    · rw [e₅] at hf
      exact h.frame.trans (hf.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨bR s₀, by simp, b256_sub s₀⟩
        · exact ⟨stackR s₀, by simp, fun _ h => h⟩)
    · have hce : stateAt s₁.callEntry.mem (st s₀) = stateAt s₁.mem (st s₀) := by
        rw [State.callEntry_mem]
        exact stateAt_frame (rs := [stackR s₀])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
            rw [← hstk]; exact below_call _ (by lit_omega) (by lit_omega)))
          (by simpa using hp.stk_st.symm)
      simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
        hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hm₃, hce,
        e₅, h.cnt] at hpost
      rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- How many bytes of block `j` are used. -/
abbrev C (s₀ : State) (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)

/-- With the first `i` bytes of block `j` done. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = sp s₀ + BitVec.ofNat 64 (P s₀ j)
  r13 : s.gpr .r13 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rsi : s.gpr .rsi = bp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (C s₀ j)
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then X0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

set_option simprocs false in
theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
      (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)])))
      s (IInv s₀ j 0) := by
  have h₁ : WP isa (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)]) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .r12 ∧ (∀ r, r ≠ .rdx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem ∧ eval .b s₁ = some (decide (L s₀ - P s₀ j < 64)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false]
    refine ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, ?_⟩
    have se : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
    have hr : (s.gpr .r12).toNat = L s₀ - P s₀ j := by
      rw [h.r12, toNat_ofNat_lt (by have := L_lt s₀; omega)]
    simp only [eval, se, hr]
    rfl
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅, hb⟩ => ?_)
  refine WP.mono (Q := fun s₂ : State => s₂.gpr .rdx = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .rdx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.mem = s₁.mem) ?_
    fun s₂ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_
  · refine WP.ite _ hb (fun hlt => WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hge => ?_)
    · simp only [decide_eq_true_eq] at hlt
      rw [e₁, h.r12]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => by simp [State.setReg32, State.setReg, hr], rfl, rfl, rfl⟩
      simp only [State.setReg32, State.setReg, ite_true]
      rw [show C s₀ j = 64 by omega]; rfl
  · have g : ∀ r, r ≠ .rdx → s₂.gpr r = s.gpr r := fun r h₁ => by rw [f₂ r h₁, e₂ r h₁]
    have gm : s₂.mem = s.mem := f₅.trans e₅
    refine ⟨by rw [g _ (by decide), h.rbx], by rw [g _ (by decide), h.rbp],
      by rw [g _ (by decide), h.r13],
      by rw [g _ (by decide), h.r12], by rw [g _ (by decide), h.rsi], f₁, fun r hr => ?_,
      by rw [← h.rd, ← e₃, ← f₃], by rw [← h.wr, ← e₄, ← f₄], by rw [gm]; exact h.cnt,
      fun k hk => ?_, by rw [gm]; exact h.saved, by rw [gm]; exact h.frame,
      fun t ht => by rw [gm]; exact h.ks t ht⟩
    · have hr' : r ≠ .rdx := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide
      rw [g r hr']; exact h.keep r hr
    · rw [gm, h.data k hk, Nat.add_zero]

/-! ## XORing the keystream -/

/-- Byte `k` of the data, before or after block `j`: `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

/-- The destination and the source of block `j`. -/
abbrev wR (s₀ : State) (j : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (P s₀ j), C s₀ j⟩
abbrev vR (s₀ : State) (j : Nat) : Region := ⟨sp s₀ + BitVec.ofNat 64 (P s₀ j), C s₀ j⟩

theorem wR_sub (s₀ : State) {j : Nat} (hj : P s₀ j < L s₀) : Region.Sub (wR s₀ j) (dR s₀) := by
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  exact Offset.sub_base _ (by omega)

theorem vR_sub (s₀ : State) {j : Nat} (hj : P s₀ j < L s₀) : Region.Sub (vR s₀ j) (sR s₀) := by
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  exact Offset.sub_base _ (by omega)

theorem buf_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) :
    WP isa (Impl.ChaCha20.X86_64.XorBuf.xorBufTo .r13 .rbp .rsi) s (IInv s₀ j (C s₀ j)) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have sw := wR_sub s₀ hj
  have sv := vR_sub s₀ hj
  have sb : Region.Sub (⟨bp s₀, C s₀ j⟩ : Region) (bR s₀) := Region.sub_prefix (by omega)
  have hs : XorBuf.Sep (dp s₀ + BitVec.ofNat 64 (P s₀ j)) (sp s₀ + BitVec.ofNat 64 (P s₀ j)) (bp s₀) (C s₀ j) :=
    ⟨(hp.d_b.sub_left sw).sub_right sb,
      hp.alias.imp (fun e => by simp only [dp, sp] at e ⊢; rw [e]) fun hd => (hd.sub_left sv).sub_right sw,
      by omega⟩
  refine WP.mono (XorBuf.xorBufTo_ok (by decide) (by decide) (by decide) h.r13 h.rbp h.rsi h.rdx hs
    ⟨dR s₀, by simp [h.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
    ⟨sR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩)
    fun s' hq => ?_
  have F : Frame (frameR s₀) s.mem s'.mem :=
    hq.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, sw⟩
  have hd : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r ∈ [wR s₀ j], R.Disjoint r := by
    intro R hR r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hR.sub_right sw
  refine ⟨by rw [hq.keep _ (by decide) (by decide) (by decide), h.rbx],
    by rw [hq.keep _ (by decide) (by decide) (by decide), h.rbp],
    by rw [hq.keep _ (by decide) (by decide) (by decide), h.r13],
    by rw [hq.keep _ (by decide) (by decide) (by decide), h.r12],
    by rw [hq.keep _ (by decide) (by decide) (by decide), h.rsi],
    by rw [hq.keep _ (by decide) (by decide) (by decide), h.rdx], fun r hr => ?_,
    hq.rd.trans h.rd, hq.wr.trans h.wr, ?_, fun k hk => ?_, ?_, h.frame.trans F, fun t ht => ?_⟩
  · have hr' : r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [hq.keep r hr'.1 hr'.2.1 hr'.2.2]; exact h.keep r hr
  · rw [stateAt_frame hq.frame (hd _ hp.st_d), h.cnt]
  · by_cases hin : P s₀ j ≤ k ∧ k < P s₀ j + C s₀ j
    · have ea : ∀ {q : Addr}, q + BitVec.ofNat 64 k =
          q + BitVec.ofNat 64 (P s₀ j) + BitVec.ofNat 64 (k - P s₀ j) := by
        intro q; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
      rw [ea, hq.data (k - P s₀ j) (by omega), ← ea, src_of hp (p := P s₀ j)
          (fun k hk => by rw [h.data k hk, Nat.add_zero]) (h.frame) hin.1 hk,
        h.ks _ (by omega), ← ks_eq hj (i := k - P s₀ j) (by omega), Nat.add_sub_cancel' hin.1,
        ite_eq_left (by omega)]
    · rw [hq.frame _ (by
          intro r hr
          simp only [List.mem_singleton] at hr; subst hr
          simp only [Region.Contains]
          rw [Offset.toNat_sub_add _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega)]
          intro hc
          apply hin
          by_cases hkP : P s₀ j ≤ k
          · rw [show 2 ^ 64 - P s₀ j + k = k - P s₀ j + 2 ^ 64 by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)] at hc
            omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hc; omega), h.data k hk]
      by_cases hlt : k < P s₀ j
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · exact h.saved.frame hq.frame (hd _ (hp.d_b.sub_right (savR_sub s₀)).symm)
  · rw [hq.frame _ (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hp.d_b _ (sw _ hc) (contains_ofNat (by omega) (by omega)))]
    exact h.ks t ht

/-! ## The end of a block -/

def nextInstrs : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1), .store32 (at_ .rbx 48) .rax,
    .alu .add .rbp (.reg .rdx), .alu .add .r13 (.reg .rdx), .alu .sub .r12 (.reg .rdx)]

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) :
    WP isa (.block nextInstrs) s fun s' =>
      OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) := by
  have hL := L_lt s₀
  have hP := P_succ hj
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hCL : C s₀ j ≤ L s₀ - P s₀ j := Nat.min_le_right _ _
  have c₁ : (stR s₀).Contains (off (st s₀) 48) 4 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (off (st s₀) 48) 4 := ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (off (st s₀) 48) 4 := ⟨stR s₀, by simp [h.wr, hp.wr], c₁⟩
  simp only [off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nextInstrs, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load32, State.store32,
    State.setReg, State.setReg32, State.setFlags, h.rbx, i₁, o₁, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  have hv : s.mem.readW (st s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  simp only [hv]
  have hfs : Frame [stR s₀] s.mem (s.mem.writeW (off (st s₀) 48) ((ctr (S0 s₀) j)[12]'(by decide) + 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hr12 : (s.gpr .r12).toNat = L s₀ - P s₀ j := by rw [h.r12, toNat_ofNat_lt (by lit_omega)]
  have hrdx : (s.gpr .rdx).toNat = C s₀ j := by rw [h.rdx, toNat_ofNat_lt (by lit_omega)]
  refine ⟨⟨by simp (config := {decide := true}) [h.rbx], ?_, ?_, ?_, by simp (config := {decide := true}) [h.rsi],
    fun r hr => ?_, h.rd, h.wr, ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, h.rbp, h.rdx, hP, BitVec.ofNat_add,
      BitVec.add_assoc]
  · simp (config := {decide := true}) only [ite_true, ite_false, h.r13, h.rdx, hP, BitVec.ofNat_add,
      BitVec.add_assoc]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hr12, hrdx]; omega), hr12, hrdx,
      toNat_ofNat_lt (by lit_omega)]
    omega
  · have hr' : r ≠ .r12 ∧ r ≠ .r13 ∧ r ≠ .rbp ∧ r ≠ .rax := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    simp only [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2, ite_false]; exact h.keep r hr
  · dsimp only; rw [stateAt_writeW_counter, h.cnt, ctr_succ]
  · dsimp only
    rw [hfs.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (Nat.le_of_lt (L_lt s₀)) hk, h.data k hk, hP]
  · exact h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ c₁
  · have hz : (s.gpr .r12 - s.gpr .rdx == 0) = decide (L s₀ - P s₀ j - C s₀ j = 0) := by
      rw [h.r12, h.rdx, Offset.ofNat_sub_ofNat_beq (by lit_omega) (by lit_omega)]
      exact decide_eq_decide.mpr (by lit_omega)
    rw [hz, hP, Nat.sub_sub]

/-! ## A whole block -/

theorem body_eq : body =
    .seq (.block [.mov .rdi (.reg .rbx)]) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
    (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)]))
    (.seq (Impl.ChaCha20.X86_64.XorBuf.xorBufTo .r13 .rbp .rsi) (.block nextInstrs))))) := rfl

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (L s₀ - P s₀ (j + 1) = 0)) := by
  have hc := call_ok hp h
  rw [WP.seq_iff] at hc
  rw [body_eq, WP.seq_iff]
  refine WP.mono hc fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₁ fun s₂ h₂ => ?_
  have hs := sel_ok hj h₂
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (buf_ok hp hj h₄) fun s₆ h₆ => next_ok hp hj h₆)

/-! ## The epilogue -/

theorem ret_stack (s₀ : State) : (retR s₀).Disjoint (stackR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

/-- What the function does: `xorTo`'s postcondition. -/
abbrev XPost (s₀ s' : State) : Prop :=
  bytesAt s'.mem (dp s₀) (L s₀) = List.zipWith (· ^^^ ·) (bytesAt s₀.mem (sp s₀) (L s₀)) (KS s₀)

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa (.block restore) s fun s' =>
      (gprPreserved s₀ s' ∧ XPost s₀ s') ∧ s'.gpr .rsi = bp s₀ := by
  refine WP.mono (Spill.restore_ok .rsi saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.rsi]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := saved_bound p hp'
    rw [h.rsi]
    exact ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], Offset.contains_base _ (by omega) (by lit_omega)⟩
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, by rw [h₂ _ (by decide), h.rsi]⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · exact h₁ r hs
    · rw [h₂ r hs]
      revert hs; revert r; exact fun r hr hs => h.keep r (by revert r hr; decide)
  · show s'.mem.readW _ _ = _
    rw [hm]
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_d
    · exact hp.ret_b
    · exact ret_stack s₀
  · show bytesAt s'.mem _ _ = _
    rw [hm]
    refine bytesAt_xor_to (length_keystream _ _) fun k hk => ?_
    have hk' : k < L s₀ := hk
    rw [h.data k hk']
    simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Xor.xor =
    .seq (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .r8), .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore)) := rfl

theorem correct {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.X86_64.Xor.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ XPost s₀ s') ∧ s'.gpr .rsi = bp s₀ := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => epilogue_ok hp hj h₂)
  refine WP.ite (decide (L s₀ = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by simp [P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (body_ok hp hj hI) fun s' ⟨h', hz'⟩ => ?_
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by simp [eval, hz', hl], j + 1, by omega, h'⟩
      · exact .inr ⟨by simp [eval, hz', hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁⟩

/-- `vg_chacha20_xor` is correct, and returns with `rsi` pointing at `buf`, for
a caller that recomputes pointers from it. -/
theorem xor_to (s : State) (hs : (Proof.ChaCha20.xorTo 8).pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorTo 8).post s s' := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := correct (XPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2, hr⟩

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the lengths
of `state` and `buf` (the destination's varies) and the registers holding
their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.r8, 1, 0), (.rcx, 2, 0)] }

theorem agree₀ {k : Nat} {s₁ s₂ : State} (h₁ : (Proof.ChaCha20.xorTo k).pre s₁)
    (h₂ : (Proof.ChaCha20.xorTo k).pre s₂) (hpub : (Proof.ChaCha20.xorTo k).pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (Proof.ChaCha20.xorTo k).pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, -, d1, d2, -, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .rdx).isLt]⟩,
      fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3, p4, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

theorem xor_ctTo : ConstantTime isa (Proof.ChaCha20.xorTo 8).pre (Proof.ChaCha20.xorTo 8).pub
    Impl.ChaCha20.X86_64.Xor.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- `vg_chacha20_xor` called in place. -/
theorem xor_in : ∀ s, (Proof.ChaCha20.xorIn 8).pre s →
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorIn 8).post s s' :=
  Proof.ChaCha20.okIn_of_okTo xor_to

theorem xor_ct : ConstantTime isa (Proof.ChaCha20.xorIn 8).pre (Proof.ChaCha20.xorIn 8).pub
    Impl.ChaCha20.X86_64.Xor.xor :=
  Proof.ChaCha20.ctIn_of_ctTo xor_to xor_ctTo

end VG.Proof.ChaCha20.X86_64.Xor
