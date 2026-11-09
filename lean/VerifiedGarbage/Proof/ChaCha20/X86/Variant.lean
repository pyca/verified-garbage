module

public import VerifiedGarbage.Proof.ChaCha20.X86.Xor
public import VerifiedGarbage.Impl.ChaCha20.X86.Callee
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# Implementations of `vg_chacha20_xor` on x86 (32-bit)

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on x86 (`Variants/ChaCha20Xor/X86/`), and each caller
(in `Generic/ChaCha20Xor/X86/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation has the contract `xorX86`, with the
12 bytes of stack below its return address.

A caller calls one in a frame of its four arguments with `dst` in `esi`
(`XorCall`): `XorImpl.call_to` gives its effect from the source to the
destination, `XorImpl.call` in place, and `XorImpl.rel` that the call is
constant time when two runs pass the same arguments.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86

open VG.X86

/-- An implementation of `vg_chacha20_xor` on x86. -/
structure XorImpl where
  /-- Its symbol and code. -/
  callee : Impl.ChaCha20.X86.Callee
  /-- It is correct. -/
  ok : ∀ s, Proof.ChaCha20.xorX86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.xorX86.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub callee.code
  /-- It never writes the stack pointer, and its calls and frames use 12 bytes of stack. -/
  nosp : NoSp callee.code
  stack : stackUse callee.code = 12
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_ssse3`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XorImpl

/-- `vg_chacha20_xor`, with SSE2 (the baseline ISA). -/
def sse2 : XorImpl where
  callee := .sse2
  ok := Xor.xor_correct
  ct := Xor.xor_ct
  nosp := NoSp.of_all (by lit_decide)
  stack := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

/-- `vg_chacha20_xor_ssse3`, with SSSE3. -/
def ssse3 : XorImpl where
  callee := .ssse3
  ok := Xor.xorSsse3_correct
  ct := Xor.xorSsse3_ct
  nosp := NoSp.of_all (by lit_decide)
  stack := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ssse3"
  features := ["ssse3"]

end XorImpl

/-! ## Calling an implementation -/

/-- The regions the callee may read, and write, from the caller's: the
source; the state, the destination, `buf` and the frame of arguments. -/
abbrev xorRd (S : BitVec 32) (n : Nat) : List Region := [⟨S.setWidth 64, n⟩]
abbrev xorWr (E St D B : BitVec 32) (n : Nat) : List Region :=
  [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩, below E 16]

/-- A call of `vg_chacha20_xor(state, src, len, buf)` (the arguments in `rt`,
`rx`, `rn` and `rb`, pushed last to first, `dst` in `esi`) from a state with
`esp` at `E`, below which the call uses 32 bytes (its frame, the return
address and the 12 bytes the callee uses below that): `xorX86`'s
precondition, in terms of the caller's regions. -/
structure XorCall (s : State) (rb rn rx rt : Reg) (E St S D B : BitVec 32) (n : Nat) : Prop where
  esp : s.gpr .esp = E
  hrt : s.gpr rt = St
  hrx : s.gpr rx = S
  hrn : s.gpr rn = BitVec.ofNat 32 n
  hrb : s.gpr rb = B
  esi : s.gpr .esi = D
  regs : Reg.esp ∉ [rb, rn, rx, rt]
  sp_lo : 32 ≤ E.toNat
  n_lt : n < 2 ^ 32
  st_fit : St.toNat + 64 ≤ 2 ^ 32
  s_fit : S.toNat + n ≤ 2 ^ 32
  d_fit : D.toNat + n ≤ 2 ^ 32
  b_fit : B.toNat + 320 ≤ 2 ^ 32
  st_s : (⟨St.setWidth 64, 64⟩ : Region).Disjoint ⟨S.setWidth 64, n⟩
  st_d : (⟨St.setWidth 64, 64⟩ : Region).Disjoint ⟨D.setWidth 64, n⟩
  st_b : (⟨St.setWidth 64, 64⟩ : Region).Disjoint ⟨B.setWidth 64, 320⟩
  s_b : (⟨S.setWidth 64, n⟩ : Region).Disjoint ⟨B.setWidth 64, 320⟩
  d_b : (⟨D.setWidth 64, n⟩ : Region).Disjoint ⟨B.setWidth 64, 320⟩
  /-- In place, or apart. -/
  alias : D = S ∨ (⟨S.setWidth 64, n⟩ : Region).Disjoint ⟨D.setWidth 64, n⟩
  stk_st : (below E 32).Disjoint ⟨St.setWidth 64, 64⟩
  stk_s : (below E 32).Disjoint ⟨S.setWidth 64, n⟩
  stk_d : (below E 32).Disjoint ⟨D.setWidth 64, n⟩
  stk_b : (below E 32).Disjoint ⟨B.setWidth 64, 320⟩
  cov : Covers (xorRd S n ++ [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩]) (s.rd ++ s.wr)
  covw : Covers [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩] s.wr

namespace XorCall

variable {s : State} {rb rn rx rt : Reg} {E St S D B : BitVec 32} {n : Nat}
  (h : XorCall s rb rn rx rt E St S D B n)
include h

theorem fit : 4 * [rb, rn, rx, rt].length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := h.sp_lo; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed [rb, rn, rx, rt] s).callEntry 0 = St ∧
    arg (pushed [rb, rn, rx, rt] s).callEntry 1 = S ∧
    arg (pushed [rb, rn, rx, rt] s).callEntry 2 = BitVec.ofNat 32 n ∧
    arg (pushed [rb, rn, rx, rt] s).callEntry 3 = B :=
  ⟨by rw [callEntry_arg h.fit h.regs (by simp)]; exact h.hrt,
   by rw [callEntry_arg h.fit h.regs (by simp)]; exact h.hrx,
   by rw [callEntry_arg h.fit h.regs (by simp)]; exact h.hrn,
   by rw [callEntry_arg h.fit h.regs (by simp)]; exact h.hrb⟩

theorem esi' : (pushed [rb, rn, rx, rt] s).callEntry.gpr .esi = D := by
  rw [callEntry_gpr' _ _ (by decide)]; exact h.esi

/-- Part of the 32 bytes below `E`. -/
theorem stk_part {a k : Nat} (hk : k ≤ a) (ha : a ≤ 32) :
    Region.Sub ⟨(E - BitVec.ofNat 32 a).setWidth 64, k⟩ (below E 32) :=
  fun x hx => below_sub ha h.sp_lo x (Region.sub_prefix hk x hx)

/-- The callee's precondition. -/
theorem callPre : CallPre Proof.ChaCha20.xorX86 [rb, rn, rx, rt] (xorRd S n) (xorWr E St D B n) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hn : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.n_lt
  have hlo := h.sp_lo
  have hE := E.isLt
  have es : (E - BitVec.ofNat 32 20).setWidth 64 - 12 = (E - BitVec.ofNat 32 32).setWidth 64 := by
    rw [VG.X86.Taint.sub_setWidth (by omega), VG.X86.Taint.sub_setWidth (by omega), BitVec.sub_sub]; rfl
  have espN : (E - BitVec.ofNat 32 20).toNat = E.toNat - 20 := sub_toNat (by omega)
  have esp64 : (pushed [rb, rn, rx, rt] s).callEntry.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [callEntry_esp', h.esp]; rfl
  have aa : argAddr (pushed [rb, rn, rx, rt] s).callEntry 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, h.esp]; rfl
  have ka : Region.Sub (below E 16) (below E 32) := h.stk_part (by omega) (by omega)
  have kr : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below E 32) := h.stk_part (by omega) (by omega)
  have ks : Region.Sub ⟨(E - BitVec.ofNat 32 32).setWidth 64, 12⟩ (below E 32) := h.stk_part (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.xorX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, h.esi', aa, esp64, espN,
      hn, es]
    exact ⟨trivial, trivial, h.st_s, h.st_d, h.st_b, h.s_b, h.d_b, h.alias,
      h.stk_st.sub_left ka, h.stk_d.sub_left ka, h.stk_b.sub_left ka,
      h.stk_st.sub_left kr, h.stk_d.sub_left kr, h.stk_b.sub_left kr,
      h.stk_st.sub_left ks, h.stk_s.sub_left ks, h.stk_d.sub_left ks, h.stk_b.sub_left ks,
      h.st_fit, h.s_fit, h.d_fit, h.b_fit, by omega, by omega⟩
  · rw [h.esp, show xorRd S n ++ xorWr E St D B n = (xorRd S n ++
      [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩]) ++ [below E 16] from rfl]
    refine Covers.append_left (h.cov.trans (Covers.of_mem fun r hr => ?_)) (Covers.of_mem fun r hr => ?_)
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_append_right _ List.mem_cons_self
  · rw [h.esp, show xorWr E St D B n =
      [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩] ++ [below E 16] from rfl]
    refine Covers.append_left (h.covw.trans (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact List.mem_cons_self

end XorCall

/-- Bytes outside a frame are unchanged. -/
theorem xor_bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.ChaCha20.bytesAt m' p n = Spec.ChaCha20.bytesAt m p n := by
  simp only [Spec.ChaCha20.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

namespace XorImpl

variable {s : State} {rb rn rx rt : Reg} {E St S D B : BitVec 32} {n : Nat}

/-- A call of an implementation: the source XORed with the keystream into
the destination; the memory changes only in the state, the destination,
`buf` and the 32 bytes below `esp`. -/
theorem call_to (v : XorImpl) (h : XorCall s rb rn rx rt E St S D B n) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨St.setWidth 64, 64⟩, ⟨D.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩, below E 32] s.mem s'.mem →
      Spec.ChaCha20.bytesAt s'.mem (D.setWidth 64) n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (S.setWidth 64) n)
          (Spec.ChaCha20.keystream (Spec.ChaCha20.stateAt s.mem (St.setWidth 64)) n) → Q s') :
    WP isa (.frame (.push [rb, rn, rx, rt]) (.call v.callee.name v.callee.code) (.pop .eax 4)) s Q := by
  have hlo := h.sp_lo
  refine WP.callWith v.ok v.nosp (by simp) h.regs
    (by rw [v.stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [v.stack, h.esp] at f'
  refine hQ s' rd' wr' cs' (f'.sub fun r hr => ?_) ?_
  · simp only [xorWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below E 32, by simp, below_sub (by omega) hlo⟩
    · exact ⟨below E 32, by simp, below_sub (by omega) hlo⟩
  · obtain ⟨a0, a1, a2, -⟩ := h.args
    have hn : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.n_lt
    simp only [Proof.ChaCha20.xorX86, arg_withRegions, State.withRegions_mem, State.withRegions_gpr, a0, a1, a2,
      h.esi', hn, m₂] at post
    have ef : Frame [below E 32] s.mem (pushed [rb, rn, rx, rt] s).callEntry.mem :=
      (callEntry_frame h.fit h.regs).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [h.esp]; exact below_sub (by simp only [List.length_cons, List.length_nil]; omega) hlo⟩
    rw [post, xor_bytesAt_frame ef (by simpa using h.stk_s.symm) (by have := h.n_lt; omega),
      Xor.stateAt_frame ef (by simpa using h.stk_st.symm)]

/-- A call of an implementation in place (`dst = src`). -/
theorem call (v : XorImpl) (h : XorCall s rb rn rx rt E St S S B n) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨St.setWidth 64, 64⟩, ⟨S.setWidth 64, n⟩, ⟨B.setWidth 64, 320⟩, below E 32] s.mem s'.mem →
      Spec.ChaCha20.bytesAt s'.mem (S.setWidth 64) n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (S.setWidth 64) n)
          (Spec.ChaCha20.keystream (Spec.ChaCha20.stateAt s.mem (St.setWidth 64)) n) → Q s') :
    WP isa (.frame (.push [rb, rn, rx, rt]) (.call v.callee.name v.callee.code) (.pop .eax 4)) s Q :=
  v.call_to h hQ

/-- Two runs that make the call with the same arguments make it in constant time. -/
theorem rel (v : XorImpl) {P : State → State → Prop}
    (hP : ∀ x y, P x y → XorCall x rb rn rx rt E St S D B n ∧ XorCall y rb rn rx rt E St S D B n) :
    RelCT isa P (.frame (.push [rb, rn, rx, rt]) (.call v.callee.name v.callee.code) (.pop .eax 4))
      fun _ _ => True := by
  refine RelCT.callWith v.ok v.ct (xorRd S n) (xorWr E St D B n) fun x y hxy => ?_
  obtain ⟨hx, hy⟩ := hP x y hxy
  obtain ⟨x0, x1, x2, x3⟩ := hx.args
  obtain ⟨y0, y1, y2, y3⟩ := hy.args
  refine ⟨hx.callPre, hy.callPre, by rw [hx.esp, hy.esp], ?_, fun i hi => ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', hx.esp, hy.esp]
  · simp only [arg_withRegions]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [x0, y0]
    · rw [x1, y1]
    · rw [x2, y2]
    · rw [x3, y3]
  · simp only [State.withRegions_gpr, hx.esi', hy.esi']

end XorImpl

end VG.Proof.ChaCha20.X86
