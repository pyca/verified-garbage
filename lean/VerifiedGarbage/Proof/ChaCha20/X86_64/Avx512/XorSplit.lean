module
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.SymSel

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.FinishSel
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer on x86-64 with AVX-512: the loop

The contract the proof of `vg_chacha20_xor_split_avx512` is written against
(`xorSplitX86_64`), and its loop over 1024-byte chunks (`bodySel_ok`).

The proof runs against the state `V s₀`, in which `vg_chacha20_xor_avx512`
would XOR in place what this function XORs: its data is `dst`, holding the
input `I s₀` (the `src_len` bytes at `src`, then the bytes of `dst` after
them), and the rest is as on entry. The in-place proofs about it
(`Avx2.APre (V s₀)`, `Avx512.ctx_of`, `Avx512.next_ok`, …) then serve here
too. The loop's invariant (`SInv`) holds the output for the chunks done,
and for the rest the bytes of `dst` from `C` on, which are the input's;
before `C`, the input is in `src`, which is never written.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_xor_split(state: *mut [u32; 16],
src: *const u8, src_len: usize, dst: *mut u8, len: usize,
buf: *mut [u32; 80])` (`state = rdi, src = rsi, src_len = rdx, dst = rcx,
len = r8, buf = r9`): if `src_len ≤ len`, writes to the `len` bytes at
`dst` the `src_len` bytes at `src` and then the bytes at `dst` after them,
XORed with the first `len` bytes of the keystream of the state at `state`.

The code may read `src` and read and write `state` (64 bytes; its contents
on exit are unspecified), `dst` and `buf` (320 bytes of working space). The
writable ones may not overlap each other, `src`, the return address on the
stack, or the 24 bytes below it, which its call uses; `src` and `dst` do not
wrap around the end of the address space. The pointers and the lengths are
public; the state and the data are secret. -/
def xorSplitX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let src : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let dst : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let buf : Region := ⟨s.gpr .r9, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [src] ∧ s.wr = [state, dst, buf] ∧ (s.gpr .rdx).toNat ≤ (s.gpr .r8).toNat ∧
    state.Disjoint dst ∧ state.Disjoint buf ∧ dst.Disjoint buf ∧
    src.Disjoint state ∧ src.Disjoint dst ∧ src.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint dst ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint dst ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      List.zipWith (· ^^^ ·)
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat ++
          (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).drop (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (Ctx SelOk srcR Incs ZH setup_ok rounds_ok finishSel_ok regn baseR bsize
  wregs incs_mem consts_eq cmp_ok saveR incR save_sub inc_sub inc_save win_sub out_win ks_shift)
open VG.Proof.ChaCha20.X86_64.Avx2 (add_ofNat)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev sst : Addr := s₀.gpr .rdi
abbrev ssp : Addr := s₀.gpr .rsi
abbrev sS : Nat := (s₀.gpr .rdx).toNat
abbrev sdp : Addr := s₀.gpr .rcx
abbrev sL : Nat := (s₀.gpr .r8).toNat
abbrev sbp : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨sst s₀, 64⟩
abbrev srR : Region := ⟨ssp s₀, sS s₀⟩
abbrev sdR : Region := ⟨sdp s₀, sL s₀⟩
abbrev bufR : Region := ⟨sbp s₀, 320⟩
abbrev sret : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev sstk : Region := below (s₀.gpr .rsp) 24
/-- Byte `k` of the input: of `src`, then of `dst`. -/
def I (k : Nat) : Byte := if k < sS s₀ then s₀.mem (ssp s₀ + BitVec.ofNat 64 k) else s₀.mem (sdp s₀ + BitVec.ofNat 64 k)
end

theorem sL_lt (s₀ : State) : sL s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
theorem sS_lt (s₀ : State) : sS s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

/-- What the proof uses of the precondition. -/
structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [srR s₀]
  wr : s₀.wr = [stR s₀, sdR s₀, bufR s₀]
  le : sS s₀ ≤ sL s₀
  st_d : (stR s₀).Disjoint (sdR s₀)
  st_b : (stR s₀).Disjoint (bufR s₀)
  d_b : (sdR s₀).Disjoint (bufR s₀)
  s_st : (srR s₀).Disjoint (stR s₀)
  s_d : (srR s₀).Disjoint (sdR s₀)
  s_b : (srR s₀).Disjoint (bufR s₀)
  ret_st : (sret s₀).Disjoint (stR s₀)
  ret_d : (sret s₀).Disjoint (sdR s₀)
  ret_b : (sret s₀).Disjoint (bufR s₀)
  stk_st : (sstk s₀).Disjoint (stR s₀)
  stk_d : (sstk s₀).Disjoint (sdR s₀)
  stk_b : (sstk s₀).Disjoint (bufR s₀)
  wrap_s : (ssp s₀).toNat + sS s₀ ≤ 2 ^ 64
  wrap_d : (sdp s₀).toNat + sL s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : xorSplitX86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## The state in which the data is XORed in place -/

/-- `dst` holding the input. -/
def vmem (s₀ : State) : Mem := fun a =>
  if (a - sdp s₀).toNat < sL s₀ then I s₀ (a - sdp s₀).toNat else s₀.mem a

/-- The arguments of `vg_chacha20_xor_avx512` for `dst`. -/
def vgpr (s₀ : State) : Reg → BitVec 64
  | .rsi => sdp s₀
  | .rdx => s₀.gpr .r8
  | .rcx => sbp s₀
  | r => s₀.gpr r

/-- `vg_chacha20_xor_avx512`'s entry state, XORing the input into `dst`. -/
def V (s₀ : State) : State := { s₀ with gpr := vgpr s₀, mem := vmem s₀ }

@[simp] theorem V_rdi (s₀ : State) : (V s₀).gpr .rdi = sst s₀ := rfl
@[simp] theorem V_rsi (s₀ : State) : (V s₀).gpr .rsi = sdp s₀ := rfl
@[simp] theorem V_rdx (s₀ : State) : (V s₀).gpr .rdx = s₀.gpr .r8 := rfl
@[simp] theorem V_rcx (s₀ : State) : (V s₀).gpr .rcx = sbp s₀ := rfl
@[simp] theorem V_rsp (s₀ : State) : (V s₀).gpr .rsp = s₀.gpr .rsp := rfl
@[simp] theorem V_rd (s₀ : State) : (V s₀).rd = s₀.rd := rfl
@[simp] theorem V_wr (s₀ : State) : (V s₀).wr = s₀.wr := rfl
@[simp] theorem V_mem (s₀ : State) : (V s₀).mem = vmem s₀ := rfl

theorem V_keep (s₀ : State) {r : Reg} (hr : r ∈ calleeSaved) : (V s₀).gpr r = s₀.gpr r := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem vmem_dst (s₀ : State) {k : Nat} (hk : k < sL s₀) :
    vmem s₀ (sdp s₀ + BitVec.ofNat 64 k) = I s₀ k := by
  have h := sL_lt s₀
  have e : (sdp s₀ + BitVec.ofNat 64 k - sdp s₀).toNat = k := by
    rw [show sdp s₀ + BitVec.ofNat 64 k - sdp s₀ = BitVec.ofNat 64 k by bv_omega, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  simp only [vmem, e, hk, ite_true]

theorem vmem_out (s₀ : State) {a : Addr} (ha : ¬ (sdR s₀).Contains a 1) : vmem s₀ a = s₀.mem a := by
  simp only [Region.Contains] at ha
  simp only [vmem, ite_eq_right_iff]
  intro h; exact absurd (by omega) ha

/-- `vmem` is the memory on entry outside `dst`. -/
theorem vmem_frame (s₀ : State) : Frame [sdR s₀] (vmem s₀) s₀.mem := fun _ hx =>
  (vmem_out s₀ (hx _ (List.mem_singleton_self _))).symm

theorem V_APre {s₀ : State} (hp : APre s₀) : Avx2.APre (V s₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Avx2.frR, Avx2.stR, Avx2.est, Avx2.edR, Avx2.edp, Avx2.eL, Avx2.bufR, Avx2.ebp, Avx2.eret,
      Avx2.estk, V_rdi, V_rsi, V_rdx, V_rcx, V_rsp, V_wr]
  · exact hp.wr
  · exact hp.st_d
  · exact hp.st_b
  · exact hp.d_b
  · exact hp.ret_st
  · exact hp.ret_d
  · exact hp.ret_b
  · exact hp.stk_st.sub_left (below_sub (by decide) (by decide))
  · exact hp.stk_d.sub_left (below_sub (by decide) (by decide))
  · exact hp.stk_b.sub_left (below_sub (by decide) (by decide))
  · exact hp.wrap_d

theorem V_S0 {s₀ : State} (hp : APre s₀) : Avx2.S0 (V s₀) = stateAt s₀.mem (sst s₀) := by
  show stateAt (vmem s₀) (sst s₀) = _
  exact (Xor.stateAt_frame (vmem_frame s₀) (p := sst s₀) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.st_d)).symm

theorem V_D0 (s₀ : State) {k : Nat} (hk : k < sL s₀) : Avx2.D0 (V s₀) k = I s₀ k := vmem_dst s₀ hk

/-- The frame of the in-place proofs, from that of this function. -/
theorem V_frame {s₀ : State} {m : Mem} (hf : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem m) :
    Frame (Avx2.frR (V s₀)) (V s₀).mem m := fun x hx => by
  have h₂ : ¬ (sdR s₀).Contains x 1 := hx _ (by simp [Avx2.frR, Avx2.edR, Avx2.edp, Avx2.eL])
  rw [hf x (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (by simp [Avx2.frR, Avx2.stR, Avx2.est])
    · exact h₂
    · exact hx _ (by simp [Avx2.frR, Avx2.bufR, Avx2.ebp])), V_mem, vmem_out s₀ h₂]

/-- The input, outside the regions written. -/
theorem src_frame {s₀ : State} (hp : APre s₀) {m : Mem} (hf : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem m) {k : Nat}
    (hk : k < sS s₀) : m (ssp s₀ + BitVec.ofNat 64 k) = s₀.mem (ssp s₀ + BitVec.ofNat 64 k) := by
  have c : (srR s₀).Contains (ssp s₀ + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by have := hp.wrap_s; omega)
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fun hc => hp.s_st _ c hc
  · exact fun hc => hp.s_d _ c hc
  · exact fun hc => hp.s_b _ c hc

/-! ## The loop invariant -/

/-- Before chunk `t`: the first `1024 t` bytes of the output written; from
`C` on, `dst` holds the input. -/
structure SInv (s₀ : State) (C t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = sst s₀
  rcx : s.gpr .rcx = sbp s₀
  rsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (sL s₀ - 1024 * t)
  r8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 (1024 * t)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (C - 1024 * t)
  le : 1024 * t ≤ sL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (sst s₀) = ctr (stateAt s₀.mem (sst s₀)) (16 * t)
  done : ∀ k < 1024 * t, s.mem (sdp s₀ + BitVec.ofNat 64 k) =
    I s₀ k ^^^ (keystream (stateAt s₀.mem (sst s₀)) (sL s₀)).getD k 0
  todo : ∀ k < sL s₀, 1024 * t ≤ k → C ≤ k → s.mem (sdp s₀ + BitVec.ofNat 64 k) = I s₀ k
  incs : Incs s.mem (sbp s₀)
  tincs : Avx512Tail.Incs s.mem (sbp s₀)
  frame : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s.mem

/-- What `C` is: a multiple of 64 within `src`. -/
structure COk (s₀ : State) (C : Nat) : Prop where
  dvd : C % 64 = 0
  le : C ≤ sS s₀

/-! ## The end of a chunk -/

theorem subSat_ok (s : State) {n c : Nat} (hn : n < 2 ^ 31) (hc : c < 2 ^ 64)
    (hr : s.gpr .r10 = BitVec.ofNat 64 c) :
    WP isa (.block (subSat n)) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (c - n) ∧ (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r p, Avx512.zw s' r p = Avx512.zw s r p) := by
  apply WP.of_runBlock
  simp only [subSat, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execCmov, eval, arithFlags, State.setReg, State.setReg32, State.setFlags, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', Avx512.signExtend_ofNat hn, reduceCtorEq,
    ↓reduceIte, hr]
  have ec : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  have en : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [ec, en]
  by_cases hcn : c < n
  · simp only [hcn, decide_true, ↓reduceIte]
    refine ⟨?_, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial, fun _ _ => rfl⟩
    rw [Nat.sub_eq_zero_of_le (by omega)]; rfl
  · simp only [hcn, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by bv_omega, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial, fun _ _ => rfl⟩

set_option simprocs false in
theorem addR8_ok (s : State) {n : Nat} (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add .r8 (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r p, Avx512.zw s' r p = Avx512.zw s r p) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left',
    Avx512.signExtend_ofNat hn]
  exact ⟨by simp, fun r h => by simp [h], trivial, trivial, trivial, fun _ _ => rfl⟩

/-- `src` and `r10` on, before `next`. -/
theorem advSel_ok (s : State) {n c : Nat} (hn : n < 2 ^ 31) (hc : c < 2 ^ 64) (hr : s.gpr .r10 = BitVec.ofNat 64 c) :
    WP isa (.block (([.alu .add .r8 (.imm (BitVec.ofNat 32 n))] : List Instr) ++ subSat n)) s fun s' =>
      s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 n ∧ s'.gpr .r10 = BitVec.ofNat 64 (c - n) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r p, Avx512.zw s' r p = Avx512.zw s r p) :=
  WP.block_append (WP.mono (addR8_ok s hn) fun s₁ ⟨r8₁, g₁, m₁, rd₁, wr₁, z₁⟩ =>
    WP.mono (subSat_ok s₁ hn hc (by rw [g₁ _ (by decide)]; exact hr)) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, z₂⟩ =>
      ⟨by rw [g₂ _ (by decide) (by decide), r8₁], r10₂, fun r a b c => by rw [g₂ r a c, g₁ r b],
        m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁, fun r p => (z₂ r p).trans (z₁ r p)⟩)

/-! ## The chunk -/

/-- The bytes of `src` a chunk may load are in `src`. -/
theorem src_contains {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat} {a : Addr} {n : Nat}
    (hn : 0 < n)
    (h : (⟨ssp s₀ + BitVec.ofNat 64 (1024 * t), min (C - 1024 * t) 1024⟩ : Region).Contains a n) :
    (srR s₀).Contains a n := by
  have hw := hp.wrap_s
  have hc := hC.le
  have hS := sS_lt s₀
  simp only [Region.Contains] at h ⊢
  have e : (a - ssp s₀).toNat = (a - (ssp s₀ + BitVec.ofNat 64 (1024 * t))).toNat + 1024 * t := by
    have : 1024 * t < 2 ^ 64 := by omega
    bv_omega
  omega

theorem selOk_of {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat} (hw : 1024 * t + 1024 ≤ sL s₀)
    {s : State} (hrcx : s.gpr .rcx = sbp s₀) (hrsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t))
    (hr8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 (1024 * t)) (hr10 : s.gpr .r10 = BitVec.ofNat 64 (C - 1024 * t))
    (hrd : s.rd = s₀.rd) : SelOk s := by
  have hS := sS_lt s₀
  have e10 : (s.gpr .r10).toNat = C - 1024 * t := by
    rw [hr10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hC.le; omega)]
  have sr : srcR s = ⟨ssp s₀ + BitVec.ofNat 64 (1024 * t), min (C - 1024 * t) 1024⟩ := by
    simp only [srcR, hr8, e10]
  have sub : Region.Sub (srcR s) (srR s₀) := fun a ha => by
    rw [sr] at ha; exact src_contains hp hC (by decide) ha
  refine ⟨fun a n hn ha => ?_, fun r hr => ?_⟩
  · rw [hrd, hp.rd]; rw [sr] at ha
    exact ⟨srR s₀, by simp, src_contains hp hC hn ha⟩
  · simp only [wregs, hrcx, hrsi, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.s_b.sub_left sub).sub_right (Region.sub_prefix (by omega))
    · exact (hp.s_d.sub_left sub).sub_right (win_sub (s₀ := V s₀) hw)

theorem bodySel_eq : bodySel = .seq (.block setup) (.seq (rounds 10) (.seq (pieces finishSel)
    (.block (([.alu .add .r8 (.imm (BitVec.ofNat 32 1024))] : List Instr) ++ subSat 1024 ++ next)))) := rfl

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r10 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Byte `k` of a chunk's input, as the chunk loads it. -/
theorem sel_byte {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat} {s : State} (h : SInv s₀ C t s)
    {k : Nat} (hk : k < 1024) (hkL : 1024 * t + k < sL s₀) :
    (if 64 * (k / 64) + 64 ≤ (BitVec.ofNat 64 (C - 1024 * t)).toNat then
        s.mem (ssp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 k)
      else s.mem (sdp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 k)) = I s₀ (1024 * t + k) := by
  have hS := sS_lt s₀
  have hCS := hC.le
  have hC64 := hC.dvd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), add_ofNat, add_ofNat]
  split
  · rename_i hb
    rw [src_frame hp h.frame (by omega)]
    simp only [I, show 1024 * t + k < sS s₀ by omega, ite_true]
  · rename_i hb
    exact h.todo _ hkL (by omega) (by omega)

theorem bodySel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat}
    (hge : 1024 ≤ sL s₀ - 1024 * t) {s : State} (h : SInv s₀ C t s) :
    WP isa bodySel s fun s' =>
      SInv s₀ C (t + 1) s' ∧ s'.cf = some (decide (sL s₀ - 1024 * (t + 1) < 1024)) := by
  have hV := V_APre hp
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  have hCS := hC.le
  have hw : 1024 * t + 1024 ≤ sL s₀ := by omega
  have sw := win_sub (s₀ := V s₀) hw
  have dsd := hV.st_d.sub_right sw
  have dbd := hV.d_b.symm.sub_right sw
  have hc : Ctx s := Avx512.ctx_of hV hw h.rdi h.rcx h.rsi h.wr
  have hi : Incs s.mem (s.gpr .rcx) := by rw [h.rcx]; exact h.incs
  rw [bodySel_eq]
  refine WP.seq (WP.mono (setup_ok hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx s₂ := Avx512.ctx_of hV hw (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hs₂ : SelOk s₂ := selOk_of hp hC hw (by rw [g₂]; exact h.rcx) (by rw [g₂]; exact h.rsi)
    (by rw [g₂]; exact h.r8) (by rw [g₂]; exact h.r10) (by rw [rd₂]; exact h.rd)
  have hi₂ : Incs s₂.mem (s₂.gpr .rcx) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (finishSel_ok hc₂ hs₂ hi₂ hz₂) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : wregs s₂ = [saveR (V s₀), Avx512.wR (V s₀) t] := by simp only [wregs, g₂, h.rcx, h.rsi]; rfl
  rw [ws, m₂] at f₃
  simp only [g₂, m₂, h.rsi, h.rdi, h.r8, h.r10] at d₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.block_append (WP.mono (advSel_ok s₃ (n := 1024) (c := C - 1024 * t) (by decide) (by omega)
    (by rw [g₃']; exact h.r10)) fun s₄ ⟨r8₄, r10₄, g₄, m₄, rd₄, wr₄, _⟩ => ?_)
  have gk₄ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [g₄ r a b c, g₃']
  refine WP.mono (Avx512.next_ok hV hge (by rw [gk₄ _ (by decide) (by decide) (by decide)]; exact h.rdi)
    (by rw [gk₄ _ (by decide) (by decide) (by decide)]; exact h.rsi)
    (by rw [gk₄ _ (by decide) (by decide) (by decide)]; exact h.rdx) (by rw [rd₄, rd₃, rd₂, h.rd]; rfl)
    (by rw [wr₄, wr₃, wr₂, h.wr]; rfl))
    fun s₅ ⟨e₁, e₂, e₃, e₄, f₅, rd₅, wr₅, cf₅⟩ => ⟨?_, cf₅⟩
  have dss : (Avx2.stR (sst s₀)).Disjoint (saveR (V s₀)) := hV.st_b.sub_right (save_sub _)
  rw [m₄] at f₅ e₄
  have FA : Frame [saveR (V s₀), Avx512.wR (V s₀) t, Avx2.stR (sst s₀)] s.mem s₅.mem :=
    (f₃.mono (by simp)).trans (f₅.mono (by simp))
  have hS₃ : stateAt s₃.mem (sst s₀) = stateAt s.mem (sst s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [e₃ r a b c, gk₄ r a d e]
  have n_st : ∀ k < sL s₀, ¬ (Avx2.stR (sst s₀)).Contains (sdp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.st_d _ hc (Avx2.in_dR (s₀ := V s₀) hk)
  have n_sv : ∀ k < sL s₀, ¬ (saveR (V s₀)).Contains (sdp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk) (save_sub (V s₀) _ hc)
  have keep₅ : ∀ k < sL s₀, (k < 1024 * t ∨ 1024 * t + 1024 ≤ k) →
      s₅.mem (sdp s₀ + BitVec.ofNat 64 k) = s.mem (sdp s₀ + BitVec.ofNat 64 k) := fun k hk ho =>
    FA _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact n_sv k hk
      · exact out_win (s₀ := V s₀) hw hk ho
      · exact n_st k hk)
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂,
    by rw [e₃ _ (by decide) (by decide) (by decide), r8₄, g₃', h.r8, add_ofNat, Nat.mul_succ],
    by rw [e₃ _ (by decide) (by decide) (by decide), r10₄, Nat.sub_sub, Nat.mul_succ], by omega,
    fun r hr => ?_, by rw [rd₅, rd₄, rd₃, rd₂, h.rd], by rw [wr₅, wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, fun k hk h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, d, e⟩ := calleeSaved_ne hr
    rw [gk r a b c d e]; exact h.keep r hr
  · have e₄' : stateAt s₅.mem (sst s₀) = (stateAt s₃.mem (sst s₀)).set 12 ((stateAt s₃.mem (sst s₀))[12] + 16) := e₄
    rw [e₄', hS₃, h.cnt, show 16 * (t + 1) = 16 * t + 16 by omega]
    exact Avx2.ctr_add _ _ 16
  · by_cases hin : 1024 * t ≤ k
    · have ea : sdp s₀ + BitVec.ofNat 64 k =
          sdp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin]
      have x₃ := d₃ (k - 1024 * t) (by omega)
      rw [sel_byte hp hC h (k := k - 1024 * t) (by omega) (by omega), ← ea, Nat.add_sub_cancel' hin] at x₃
      rw [f₅ _ (by simpa using n_st k (by omega)), x₃, Avx2.plus_block, h.cnt,
        ks_shift _ (by omega) hin]
    · rw [keep₅ k (by omega) (.inl (by omega)), h.done k (by omega)]
  · rw [keep₅ k hk (.inr (by omega)), h.todo k hk (by omega) h₂]
  · refine Avx512.incs_frame (s₀ := V s₀) h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact inc_save _
    · exact dbd.sub_left (inc_sub _)
    · exact (hV.st_b.sub_right (inc_sub _)).symm
  · refine Avx512Tail.incs_frame (s₀ := V s₀) h.tincs FA ?_
    have ti : Region.Sub ⟨sbp s₀ + BitVec.ofNat 64 192, 128⟩ (Avx2.bufR (sbp s₀)) := Offset.sub_base _ (by omega)
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by omega) (by omega) |>.symm
    · exact dbd.sub_left ti
    · exact (hV.st_b.sub_right ti).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨bufR s₀, by simp, save_sub _⟩
    · exact ⟨sdR s₀, by simp, sw⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩

/-! ## The loop -/

/-- The chunks, while at least 1024 bytes are left. -/
theorem loop_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {s₁ : State} (h₁ : SInv s₀ C 0 s₁)
    (hc : s₁.cf = some (decide (sL s₀ < 1024))) :
    WP isa (.ite .b (.block []) (.loop bodySel .ae)) s₁ fun s =>
      ∃ t, sL s₀ - 1024 * t < 1024 ∧ SInv s₀ C t s := by
  refine WP.ite (decide (sL s₀ < 1024)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = sL s₀ - 1024 * t ∧ 1024 ≤ sL s₀ - 1024 * t ∧ SInv s₀ C t s
    have hstep : ∀ n s, Inv n s → WP isa bodySel s (fun s' =>
        (eval .ae s' = some false ∧ ∃ t, sL s₀ - 1024 * t < 1024 ∧ SInv s₀ C t s') ∨
        (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (bodySel_ok hp hC ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : sL s₀ - 1024 * (t + 1) < 1024
      · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [eval, hc', hl], sL s₀ - 1024 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (sL s₀ - 1024 * 0) s₁ ⟨0, rfl, by omega, h₁⟩

end VG.Proof.ChaCha20.X86_64.Avx512Split
