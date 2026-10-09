import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Impl.ChaCha20.X86_64.XorTo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBufTo
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Spec.ChaCha20.OutOfPlace

/-!
# ChaCha20 keystream XOR out of place on x86-64
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_xor_to(state: *mut [u32; 16], src: *const u8,
len: usize, dst: *mut u8, dst_len: usize, buf: *mut [u32; 80])`: writes to the
`len` bytes at `dst` the `len` bytes at `src` XORed with the first `len` bytes
of the keystream of the state at `state`.

The code may read `src` (`len` bytes) and read and write `state` (64 bytes;
its contents on exit are unspecified), `dst` (`dst_len = len` bytes) and
`buf` (320 bytes of working space). They may not overlap each other, the
return address on the stack, or the 8 bytes below it, where the call of the
block function stores its return address; neither `src` nor `dst` wraps
around the end of the address space. The pointers and the lengths are
public; the state and the data are secret. -/
def xorToX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let src : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let dst : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let buf : Region := ⟨s.gpr .r9, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.gpr .r8 = s.gpr .rdx ∧ s.rd = [src] ∧ s.wr = [state, dst, buf] ∧
    state.Disjoint src ∧ state.Disjoint dst ∧ state.Disjoint buf ∧ src.Disjoint dst ∧ src.Disjoint buf ∧
    dst.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint src ∧ ret.Disjoint dst ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint src ∧ stack.Disjoint dst ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.XorTo

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.XorTo
open VG.Proof.ChaCha20.X86_64.Xor (stateAt_writeW_counter contains_ofNat stateAt_frame block_keeps_reg block_depth
  ret_stack)
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
abbrev sp : Addr := s₀.gpr .rsi
abbrev L : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev bp : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev sR : Region := ⟨sp s₀, L s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stackR : Region := below (s₀.gpr .rsp) 8
/-- The state, the data, the output and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev X0 (k : Nat) : Byte := s₀.mem (sp s₀ + BitVec.ofNat 64 k)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

structure XPre (s₀ : State) : Prop where
  r8 : s₀.gpr .r8 = s₀.gpr .rdx
  rd : s₀.rd = [sR s₀]
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_s : (stR s₀).Disjoint (sR s₀)
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  s_d : (sR s₀).Disjoint (dR s₀)
  s_b : (sR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_s : (retR s₀).Disjoint (sR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  stk_st : (stackR s₀).Disjoint (stR s₀)
  stk_s : (stackR s₀).Disjoint (sR s₀)
  stk_d : (stackR s₀).Disjoint (dR s₀)
  stk_b : (stackR s₀).Disjoint (bR s₀)
  nowrap_s : (sp s₀).toNat + L s₀ ≤ 2 ^ 64
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorToX86_64.pre s₀) : XPre s₀ := by
  have e : s₀.gpr .r8 = s₀.gpr .rdx := h.1
  simp only [Proof.ChaCha20.xorToX86_64, e] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

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

/-! ## Memory -/

theorem XPre.w_st {s₀ : State} (hp : XPre s₀) : stR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_d {s₀ : State} (hp : XPre s₀) : dR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_b {s₀ : State} (hp : XPre s₀) : bR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- The data is in none of the regions the code writes. -/
theorem XPre.s_frame {s₀ : State} (hp : XPre s₀) : ∀ r ∈ frameR s₀, (sR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.st_s.symm
  · exact hp.s_d
  · exact hp.s_b
  · exact hp.stk_s.symm

/-- The data keeps its bytes. -/
theorem XPre.src {s₀ : State} (hp : XPre s₀) {m : Mem} (hf : Frame (frameR s₀) s₀.mem m) {k : Nat}
    (hk : k < L s₀) : m (sp s₀ + BitVec.ofNat 64 k) = X0 s₀ k :=
  hf _ fun r hr hc => hp.s_frame r hr _ (Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)) hc

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .rsi (.reg .r9), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      OInv s₀ 0 s ∧ s.zf = some (decide (L s₀ = 0)) := by
  refine Spill.save_then .r9 saved (fun p hp' => ?_) ?_
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
  refine WP.call (k := Proof.ChaCha20.blockX86_64) block_correct (block_keeps_reg (by simp [Xor.kept]))
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
      by rw [hkeep .rsi (block_keeps_reg (by simp [Xor.kept])), hrsi],
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
    refine ⟨by rw [g _ (by decide), h.rbx], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.r13],
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

theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

/-- The output of block `j`. -/
abbrev wR (s₀ : State) (j : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (P s₀ j), C s₀ j⟩
/-- The data of block `j`. -/
abbrev xR (s₀ : State) (j : Nat) : Region := ⟨sp s₀ + BitVec.ofNat 64 (P s₀ j), C s₀ j⟩

theorem wR_sub (s₀ : State) {j : Nat} (hj : P s₀ j < L s₀) : Region.Sub (wR s₀ j) (dR s₀) := by
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  exact Offset.sub_base _ (by omega)

theorem xR_sub (s₀ : State) {j : Nat} (hj : P s₀ j < L s₀) : Region.Sub (xR s₀ j) (sR s₀) := by
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  exact Offset.sub_base _ (by omega)

theorem buf_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) :
    WP isa (Impl.ChaCha20.X86_64.XorBuf.xorBufTo .r13 .rbp .rsi) s (IInv s₀ j (C s₀ j)) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have sw := wR_sub s₀ hj
  have sx := xR_sub s₀ hj
  have sb : Region.Sub (⟨bp s₀, C s₀ j⟩ : Region) (bR s₀) := Region.sub_prefix (by omega)
  refine WP.mono (XorBufTo.xorBufTo_ok ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ h.r13 h.rbp h.rsi h.rdx
    ⟨(hp.s_d.symm.sub_left sw).sub_right sx, (hp.d_b.sub_left sw).sub_right sb, by omega,
      ⟨dR s₀, by simp [h.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩,
      ⟨sR s₀, by simp [h.rd, hp.rd], Offset.contains_base _ (by omega) (by omega)⟩,
      ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩⟩)
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
    · have ea : ∀ Q : Addr, Q + BitVec.ofNat 64 k =
          Q + BitVec.ofNat 64 (P s₀ j) + BitVec.ofNat 64 (k - P s₀ j) := fun Q => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
      rw [ea, hq.data (k - P s₀ j) (by omega), ← ea, hp.src h.frame hk, ite_eq_left (by omega),
        h.ks _ (by omega), ← ks_eq hj (i := k - P s₀ j) (by omega), Nat.add_sub_cancel' hin.1]
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

/-- Writing the data XORed with a keystream to another buffer, byte by byte. -/
theorem bytesAt_xor_to {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' q n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.ChaCha20.xorToX86_64.post s₀ s' := by
  refine WP.mono (Spill.restore_ok .rsi saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.rsi]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := saved_bound p hp'
    rw [h.rsi]
    exact ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], Offset.contains_base _ (by omega) (by lit_omega)⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
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

theorem xorTo_eq : Impl.ChaCha20.X86_64.XorTo.xorTo =
    .seq (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .rsi (.reg .r9), .alu .test .r12 (.reg .r12)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore)) := rfl

theorem correct {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.X86_64.XorTo.xorTo s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.ChaCha20.xorToX86_64.post s₀ s' := by
  rw [xorTo_eq]
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

theorem xorTo_correct (s : State) (hs : Proof.ChaCha20.xorToX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.XorTo.xorTo s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorToX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (XPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the lengths
of `state` and `buf` (the output's varies) and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0), (.r9, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorToX86_64.pre s₁)
    (h₂ : Proof.ChaCha20.xorToX86_64.pre s₂) (hpub : Proof.ChaCha20.xorToX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  have wf : ∀ s, Proof.ChaCha20.xorToX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, -, hw, -, d1, d2, -, -, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .r8).isLt]⟩,
      fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.2.1, h₂.2.2.1, p1, p4, p5, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x2800 | .r9 => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2800, 0⟩, ⟨0x3000, 320⟩]

theorem xorTo_ct : ConstantTime isa Proof.ChaCha20.xorToX86_64.pre Proof.ChaCha20.xorToX86_64.pub
    Impl.ChaCha20.X86_64.XorTo.xorTo :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xorTo_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.XorTo.xorTo (Spec.ChaCha20.xorToContract X86_64.abi 8) :=
  Verified.of_correct xorTo_correct xorTo_ct
    (by sig_implies [Spec.ChaCha20.xorToContract, Spec.ChaCha20.xorToSig, Spec.ChaCha20.xorToPre,
      X86_64.abi, X86_64.argRegs, Proof.ChaCha20.xorToX86_64]
      [sat] using sat)

end VG.Proof.ChaCha20.X86_64.XorTo
