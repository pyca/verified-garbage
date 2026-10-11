import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.FinishTo
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor

/-!
# ChaCha20 keystream XOR out of place on x86-64 with AVX-512: the loop

The contract the proof of `vg_chacha20_xor_to_avx512` is written against
(`xorToX86_64`), and its loop over 1024-byte chunks: each chunk XORs the
keystream into the next 1024 bytes of the input and writes them to the
output (`bodyTo_ok`), as the loop of `vg_chacha20_xor_avx512` does in place
(`Avx512/Xor.lean`).
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_xor_to(state: *mut [u32; 16],
src: *const u8, len: usize, dst: *mut u8, dst_len: usize,
buf: *mut [u32; 80])` (`state = rdi, src = rsi, len = rdx, dst = rcx,
dst_len = r8, buf = r9`): writes to the `len` bytes at `dst` the `len` bytes
at `src` XORed with the first `len` bytes of the keystream of the state at
`state`.

The code may read `src` and read and write `state` (64 bytes; its contents
on exit are unspecified), `dst` (`dst_len` bytes, which is `len`) and `buf`
(320 bytes of working space). The writable ones may not overlap each other,
`src`, the return address on the stack, or the 24 bytes below it, where its
call of `vg_chacha20_xor_avx512` stores its return address and the stack its
calls use; `src` and `dst` do not wrap around the end of the address space.
The pointers and the length are public; the state and the data are secret. -/
def xorToX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let src : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let dst : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let buf : Region := ⟨s.gpr .r9, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := below (s.gpr .rsp) 24
    s.rd = [src] ∧ s.wr = [state, dst, buf] ∧ s.gpr .r8 = s.gpr .rdx ∧
    state.Disjoint dst ∧ state.Disjoint buf ∧ dst.Disjoint buf ∧
    src.Disjoint state ∧ src.Disjoint dst ∧ src.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint dst ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint dst ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Avx512To

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (Ctx SrcOk Incs ZH setup_ok rounds_ok finishTo_ok regn baseR bsize wregs
  incPairs incPairs_le incs_mem consts_eq cmp_ok saveR incR save_sub inc_sub inc_save)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev est : Addr := s₀.gpr .rdi
abbrev esp : Addr := s₀.gpr .rsi
abbrev eL : Nat := (s₀.gpr .rdx).toNat
abbrev edp : Addr := s₀.gpr .rcx
abbrev ebp : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨est s₀, 64⟩
abbrev srR : Region := ⟨esp s₀, eL s₀⟩
abbrev edR : Region := ⟨edp s₀, eL s₀⟩
abbrev bufR : Region := ⟨ebp s₀, 320⟩
abbrev eret : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev estk : Region := below (s₀.gpr .rsp) 24
/-- The state, the input and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (est s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (esp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (eL s₀)
/-- The regions the code writes. -/
abbrev frR : List Region := [stR s₀, edR s₀, bufR s₀]
end

theorem eL_lt (s₀ : State) : eL s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

/-- What the proof uses of the precondition. -/
structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [srR s₀]
  wr : s₀.wr = frR s₀
  st_d : (stR s₀).Disjoint (edR s₀)
  st_b : (stR s₀).Disjoint (bufR s₀)
  d_b : (edR s₀).Disjoint (bufR s₀)
  s_st : (srR s₀).Disjoint (stR s₀)
  s_d : (srR s₀).Disjoint (edR s₀)
  s_b : (srR s₀).Disjoint (bufR s₀)
  ret_st : (eret s₀).Disjoint (stR s₀)
  ret_d : (eret s₀).Disjoint (edR s₀)
  ret_b : (eret s₀).Disjoint (bufR s₀)
  stk_st : (estk s₀).Disjoint (stR s₀)
  stk_d : (estk s₀).Disjoint (edR s₀)
  stk_b : (estk s₀).Disjoint (bufR s₀)
  wrap_s : (esp s₀).toNat + eL s₀ ≤ 2 ^ 64
  wrap_d : (edp s₀).toNat + eL s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : xorToX86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  simp only [h3] at h2 h4 h6 h8 h11 h14 h17
  exact ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem APre.w_st {s₀ : State} (hp : APre s₀) : stR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem APre.w_d {s₀ : State} (hp : APre s₀) : edR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem APre.w_b {s₀ : State} (hp : APre s₀) : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

/-! ## The loop invariant -/

/-- Before chunk `t`: the first `1024 t` bytes of the output written. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  r9 : s.gpr .r9 = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)
  r8 : s.gpr .r8 = esp s₀ + BitVec.ofNat 64 (1024 * t)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)
  le : 1024 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (16 * t)
  data : ∀ k < 1024 * t, s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  incs : Incs s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-- The input, outside the regions written. -/
theorem src_frame {s₀ : State} (hp : APre s₀) {m : Mem} (hf : Frame (frR s₀) s₀.mem m) {k : Nat}
    (hk : k < eL s₀) : m (esp s₀ + BitVec.ofNat 64 k) = D0 s₀ k := by
  have c : (srR s₀).Contains (esp s₀ + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by have := hp.wrap_s; omega)
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fun hc => hp.s_st _ c hc
  · exact fun hc => hp.s_d _ c hc
  · exact fun hc => hp.s_b _ c hc

/-! ## The end of a chunk -/

set_option simprocs false in
theorem nextTo_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t))
    (hr8 : s.gpr .r8 = esp s₀ + BitVec.ofNat 64 (1024 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block nextTo) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * (t + 1)) ∧
      s'.gpr .r8 = esp s₀ + BitVec.ofNat 64 (1024 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r8 → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 16) ∧
      Frame [stR s₀] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have c₁ : (stR s₀).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨stR s₀, by simp [hrd, hwr, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨stR s₀, by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nextTo, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [stR s₀] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  have e : (s.gpr .rdx - 1024).toNat = eL s₀ - 1024 * (t + 1) := by rw [hrdx]; bv_omega
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hr8]; bv_omega, by rw [hrdx]; bv_omega,
    fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄], Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk -/

section
variable {s₀ : State} {t : Nat}

/-- The 1024 bytes of chunk `t` of the output and of the input. -/
abbrev wR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), 1024⟩
abbrev vR (s₀ : State) (t : Nat) : Region := ⟨esp s₀ + BitVec.ofNat 64 (1024 * t), 1024⟩

theorem win_sub (hw : 1024 * t + 1024 ≤ eL s₀) : Region.Sub (wR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem vin_sub (hw : 1024 * t + 1024 ≤ eL s₀) : Region.Sub (vR s₀ t) (srR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem out_win (hw : 1024 * t + 1024 ≤ eL s₀) {k : Nat} (hk : k < 1024 * t) :
    ¬ (wR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

theorem in_edR (hp : APre s₀) {k : Nat} (hk : k < eL s₀) : (edR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have := hp.wrap_d; omega)

end

/-- Where a chunk runs: the regions of `Sym`, from the loop's. -/
theorem ctx_of {s₀ : State} (hp : APre s₀) {t : Nat} (hw : 1024 * t + 1024 ≤ eL s₀) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrcx : s.gpr .rcx = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)) (hwr : s.wr = s₀.wr) : Ctx s := by
  have hL := eL_lt s₀
  have r0 : regn s 0 = stR s₀ := by simp only [regn, baseR, bsize, hrdi]
  have r1 : regn s 1 = bufR s₀ := by simp only [regn, baseR, bsize, hrcx]
  have r2 : regn s 2 = wR s₀ t := by simp only [regn, baseR, bsize, hrsi]
  refine ⟨fun b i n hb h => ?_, fun b b' hb hb' ne => ?_⟩
  · rw [hwr, hp.wr]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]
      exact ⟨stR s₀, by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r1]
      exact ⟨bufR s₀, by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r2]
      exact ⟨edR s₀, by simp, by simp only [Region.Contains]; bv_omega⟩
  · have d01 := hp.st_b
    have d02 := hp.st_d.sub_right (win_sub hw)
    have d12 := hp.d_b.symm.sub_right (win_sub hw)
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | with_reducible assumption | exact d01.symm | exact d02.symm | exact d12.symm

/-- The input of a chunk: readable, and apart from what the chunk writes. -/
theorem src_of {s₀ : State} (hp : APre s₀) {t : Nat} (hw : 1024 * t + 1024 ≤ eL s₀) {s : State}
    (hrcx : s.gpr .rcx = ebp s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t))
    (hr8 : s.gpr .r8 = esp s₀ + BitVec.ofNat 64 (1024 * t)) (hrd : s.rd = s₀.rd) : SrcOk s := by
  have hL := eL_lt s₀
  have r3 : regn s 3 = vR s₀ t := by simp only [regn, baseR, bsize, hr8]
  have sv := vin_sub hw
  refine ⟨fun i n h => ?_, fun r hr => ?_⟩
  · rw [hrd, hp.rd, r3]
    show InRegions _ (esp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (4 * i)) (4 * n)
    rw [Avx512.add_ofNat']
    exact ⟨srR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · simp only [wregs, hrcx, hrsi, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [r3]
    rcases hr with rfl | rfl
    · exact (hp.s_b.sub_left sv).sub_right (Region.sub_prefix (by omega))
    · exact (hp.s_d.sub_left sv).sub_right (win_sub hw)

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Incs m (ebp s₀))
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩ : Region).Disjoint r) :
    Incs m' (ebp s₀) := by
  intro j hj
  rw [← h j hj]
  refine hf.readW (r := ⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩) ?_ hd (by decide)
  simp only [Region.Contains]; bv_omega

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .r8 ∧ r ≠ .rdx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem bodyTo_eq : bodyTo = .seq (.block setup) (.seq (rounds 10) (.block (finishTo ++ nextTo))) := rfl

theorem bodyTo_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (h : LInv s₀ t s) :
    WP isa bodyTo s fun s' =>
      LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have hw : 1024 * t + 1024 ≤ eL s₀ := by omega
  have sw := win_sub hw
  have dsd := hp.st_d.sub_right sw
  have dbd := hp.d_b.symm.sub_right sw
  have hc : Ctx s := ctx_of hp hw h.rdi h.rcx h.rsi h.wr
  have hi : Incs s.mem (s.gpr .rcx) := by rw [h.rcx]; exact h.incs
  rw [bodyTo_eq]
  refine WP.seq (WP.mono (setup_ok hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx s₂ := ctx_of hp hw (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hs₂ : SrcOk s₂ := src_of hp hw (by rw [g₂]; exact h.rcx) (by rw [g₂]; exact h.rsi)
    (by rw [g₂]; exact h.r8) (by rw [rd₂]; exact h.rd)
  have hi₂ : Incs s₂.mem (s₂.gpr .rcx) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (finishTo_ok hc₂ hs₂ hi₂ hz₂) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : wregs s₂ = [⟨ebp s₀, 128⟩, wR s₀ t] := by simp only [wregs, g₂, h.rcx, h.rsi]
  rw [ws, m₂] at f₃
  simp only [g₂, m₂, h.rsi, h.r8, h.rdi] at d₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (nextTo_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.r8) (by rw [g₃']; exact h.rdx) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₈, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have svb : Region.Sub ⟨ebp s₀, 128⟩ (bufR s₀) := Region.sub_prefix (by omega)
  have dss : (stR s₀).Disjoint ⟨ebp s₀, 128⟩ := hp.st_b.sub_right svb
  have FA : Frame [⟨ebp s₀, 128⟩, wR s₀ t, stR s₀] s.mem s₄.mem :=
    (f₃.mono (by simp)).trans (f₄.mono (by simp))
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r8 → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c d => by
    rw [e₃ r a b c d, g₃']
  have n_st : ∀ k < eL s₀, ¬ (stR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.st_d _ hc (in_edR hp hk)
  have n_sv : ∀ k < eL s₀, ¬ (⟨ebp s₀, 128⟩ : Region).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.d_b _ (in_edR hp hk) (svb _ hc)
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide)]; exact h.rcx,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide)]; exact h.r9, e₁, e₈, e₂, by omega,
    fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, d⟩ := calleeSaved_ne hr
    rw [gk r a b c d]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 16 * (t + 1) = 16 * t + 16 by omega]
    exact Avx2.ctr_add _ _ 16
  · by_cases hin : 1024 * t ≤ k
    · have ea : edp s₀ + BitVec.ofNat 64 k =
          edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [Avx512.add_ofNat', Nat.add_sub_cancel' hin]
      have ea' : esp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) =
          esp s₀ + BitVec.ofNat 64 k := by
        rw [Avx512.add_ofNat', Nat.add_sub_cancel' hin]
      have x₃ := d₃ (k - 1024 * t) (by omega)
      rw [← ea, ea', src_frame hp h.frame (by omega)] at x₃
      rw [f₄ _ (by simpa using n_st k (by omega)), x₃, Avx2.plus_block, h.cnt,
        Avx512.ks_shift _ (by omega) hin]
    · have n_w := out_win hw (k := k) (by omega)
      rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sv k (by omega)
          · exact n_w
          · exact n_st k (by omega)), h.data k (by omega)]
  · refine incs_frame h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have ib : Region.Sub ⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩ (bufR s₀) := Offset.sub_base _ (by omega)
    rcases hr' with rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by omega) (by omega) |>.symm
    · exact dbd.sub_left ib
    · exact (hp.st_b.sub_right ib).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨bufR s₀, by simp, svb⟩
    · exact ⟨edR s₀, by simp, sw⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩

/-! ## The prologue -/

theorem entryTo_ok (s₀ : State) :
    WP isa (.block entryTo) s₀ fun s =>
      (∀ r, r ≠ .r8 → r ≠ .rsi → r ≠ .rcx → s.gpr r = s₀.gpr r) ∧ s.gpr .r8 = esp s₀ ∧
      s.gpr .rsi = edp s₀ ∧ s.gpr .rcx = ebp s₀ ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  apply WP.of_runBlock
  simp only [entryTo, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ↓reduceIte]
  exact ⟨fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem prologue_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (entryTo ++ consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr))) s₀ fun s =>
      LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 1024)) := by
  have hL := eL_lt s₀
  rw [consts_eq]
  refine WP.block_append (WP.block_append (WP.mono (entryTo_ok s₀)
    fun s₀' ⟨g₀, r8₀, rsi₀, rcx₀, m₀, rd₀, wr₀⟩ => WP.mono (Avx2.pairs_ok (buf := ebp s₀) incPairs incPairs_le
      (s := s₀') rcx₀ (by rw [wr₀]; exact hp.w_b))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (cmp_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_))
  have F : Frame [bufR s₀] s₀.mem s₂.mem := by
    rw [m₂, m₁, m₀]
    exact Avx2.storeAll_frame (List.mem_singleton_self _) _ incPairs_le _
  have gk : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨by rw [gk _ (by decide), g₁ _ (by decide), g₀ _ (by decide) (by decide) (by decide)],
    by rw [gk _ (by decide), g₁ _ (by decide), rcx₀],
    by rw [gk _ (by decide), g₁ _ (by decide), g₀ _ (by decide) (by decide) (by decide)],
    by rw [gk _ (by decide), g₁ _ (by decide), rsi₀]; simp,
    by rw [gk _ (by decide), g₁ _ (by decide), r8₀]; simp,
    by rw [gk _ (by decide), g₁ _ (by decide), g₀ _ (by decide) (by decide) (by decide)]; simp,
    by omega, fun r hr => ?_,
    by rw [rd₂, rd₁, rd₀], by rw [wr₂, wr₁, wr₀], ?_, fun k hk => by omega, ?_, F.mono (by simp)⟩, ?_⟩
  · obtain ⟨a, b, -, -⟩ := calleeSaved_ne hr
    have c : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have d : r ≠ .r8 := (calleeSaved_ne hr).2.2.1
    rw [gk r a, g₁ r a, g₀ r d b c]
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [m₂, m₁]; exact incs_mem _ _
  · rw [cf₂, g₁ _ (by decide), g₀ _ (by decide) (by decide) (by decide)]

/-! ## The loop -/

theorem loop_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.seq (.block (entryTo ++ consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
      (.ite .b (.block []) (.loop bodyTo .ae))) s₀ fun s => ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s := by
  have hL := eL_lt s₀
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.ite (decide (eL s₀ < 1024)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = eL s₀ - 1024 * t ∧ 1024 ≤ eL s₀ - 1024 * t ∧ LInv s₀ t s
    have hstep : ∀ n s, Inv n s → WP isa bodyTo s (fun s' =>
        (eval .ae s' = some false ∧ ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s') ∨
        (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (bodyTo_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : eL s₀ - 1024 * (t + 1) < 1024
      · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 1024 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (eL s₀ - 1024 * 0) s₁ ⟨0, rfl, by omega, h₁⟩

end VG.Proof.ChaCha20.X86_64.Avx512To
