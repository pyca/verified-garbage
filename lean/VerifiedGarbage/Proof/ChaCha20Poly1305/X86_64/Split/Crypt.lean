module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Pre
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitVerified
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the encryption

`cryptSplit` (`Impl/ChaCha20Poly1305/X86_64/SealSplit.lean`) is `crypt` with
`vg_chacha20_xor_avx512` but for the call encrypting the data after its
first `mm` bytes, which becomes the code of `vg_chacha20_xor_split_avx512`
inline, reading the bytes `[mm, src_len)` from `src`: it writes to the data
the encryption of `PTs` (`cryptSplit_ok`). The inline code runs from its
contract (`xorSplitX86_64`), with the state's permissions narrowed to its
regions, its calls' return addresses within the 24 bytes below `rsp` that
`seal`'s call takes (`WP.inlineSp`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem sub_ofNat_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 (a - b) = BitVec.ofNat 64 b := by
  rw [Offset.ofNat_sub_ofNat (by omega), show a - (a - b) = b by omega]

/-- `stackArgAddr s₀ j`, as `rsp + 8 (j + 1)`. -/
theorem argAddr_eq (s₀ : State) (j : Nat) :
    off (s₀.gpr .rsp) (8 * (j + 1)) = stackArgAddr s₀ j := by
  rw [off_eq]; rfl

theorem in_arg2 {s₀ : State} (hT : SPre s₀) {s : State} (hrd : s.rd = s₀.rd) {j : Nat} (hj : j = 2 ∨ j = 3) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s₀ j) 8 := by
  refine ⟨arg2R s₀, by rw [hrd]; simp [hT.g2], ?_⟩
  rcases hj with rfl | rfl
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [stackArgAddr]
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1)) = s₀.gpr .rsp + BitVec.ofNat 64 (8 * (2 + 1)) +
      BitVec.ofNat 64 8 by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.contains_base _ (by lit_omega) (by lit_omega)

/-- The arguments of `vg_chacha20_xor_split_avx512` for the data after its
first `m` bytes. -/
structure SArgs (s₀ : State) (m : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 64
  rsi : s.gpr .rsi = sp s₀ + BitVec.ofNat 64 (min m (SL s₀))
  rdx : s.gpr .rdx = BitVec.ofNat 64 (SL s₀ - m)
  rcx : s.gpr .rcx = off (dp s₀) m
  r8 : s.gpr .r8 = BitVec.ofNat 64 (L s₀ - m)
  r9 : s.gpr .r9 = off (cx s₀) 128

set_option linter.unusedSimpArgs false in
/-- `splitArgs`, after `cryptArgsM`. -/
theorem splitArgs_ok {s₀ : State} (hT : SPre s₀) {m : Nat} {s : State} (h : XArgsM s₀ m s)
    (hrd : s.rd = s₀.rd) (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa (.block splitArgs) s fun s' => SArgs s₀ m s' ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  have hL9 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hm : m < 2 ^ 64 := by simp only [L] at hle; omega
  have hSL : SL s₀ < 2 ^ 64 := (stackArg s₀ 3).isLt
  have ra : s.gpr .rsi - s.gpr .r14 = BitVec.ofNat 64 m := by
    rw [h.rsi, h.r14, off_eq, Offset.add_sub_cancel_left]
  have i2 := in_arg2 hT hrd (.inl rfl)
  have i3 := in_arg2 hT hrd (.inr rfl)
  have e2 : off (s.gpr .rsp) 24 = stackArgAddr s₀ 2 := by rw [h.rsp]; exact argAddr_eq s₀ 2
  have e3 : off (s.gpr .rsp) 32 = stackArgAddr s₀ 3 := by rw [h.rsp]; exact argAddr_eq s₀ 3
  have em : (BitVec.ofNat 64 m).toNat = m := toNat_ofNat_lt hm
  have s3 : stackArg s₀ 3 = BitVec.ofNat 64 (SL s₀) := by simp [SL]
  have eS : (BitVec.ofNat 64 (SL s₀)).toNat = SL s₀ := toNat_ofNat_lt hSL
  by_cases hcn : SL s₀ < m
  · have hk : min m (SL s₀) = SL s₀ := Nat.min_eq_right (Nat.le_of_lt hcn)
    apply WP.of_runBlock
    simp only [splitArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execCmov, eval, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, reduceCtorEq, ↓reduceIte,
    e2, e3, i2, i3, hS2, hS3, ra, s3, em, eS, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', hcn, decide_true]
    refine ⟨⟨by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rdi], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, hk],
      by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, BitVec.sub_self, Nat.sub_eq_zero_of_le (Nat.le_of_lt hcn)],
      by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsi], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rdx], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rcx]⟩,
      fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte]
  · have hk : min m (SL s₀) = m := Nat.min_eq_left (by omega)
    apply WP.of_runBlock
    simp only [splitArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execCmov, eval, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, reduceCtorEq, ↓reduceIte,
    e2, e3, i2, i3, hS2, hS3, ra, s3, em, eS, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', hcn, decide_false, Bool.false_eq_true]
    refine ⟨⟨by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rdi], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, hk],
      by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, Offset.ofNat_sub_ofNat (show m ≤ SL s₀ by omega)],
      by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsi], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rdx], by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rcx]⟩,
      fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte]

/-! ## `vg_chacha20_xor_split_avx512`, inline -/

theorem xorSplit_nosp : NoSp Impl.ChaCha20.X86_64.Avx512.xorSplit := by
  have : ((instrs Impl.ChaCha20.X86_64.Avx512.xorSplit).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem xorSplit_depth : Impl.ChaCha20.X86_64.Avx512.xorSplit.depth ≤ 3 := by lit_decide

/-- The regions the inline code may read and write: the bytes of `src` from
`m` on, and the state, the data from `m` on and `buf`. -/
abbrev srcM (s₀ : State) (m : Nat) : Region := ⟨sp s₀ + BitVec.ofNat 64 (min m (SL s₀)), SL s₀ - m⟩
abbrev wrM (s₀ : State) (m : Nat) : List Region := [⟨off (cx s₀) 64, 64⟩, dRm s₀ m, ⟨off (cx s₀) 128, 320⟩]

/-- `srcM` lies within `src`, at offset `min m src_len`. -/
theorem srcM_in (s₀ : State) (m : Nat) :
    (srcM s₀ m).base = (spR s₀).base + BitVec.ofNat 64 (min m (SL s₀)) ∧
      min m (SL s₀) + (srcM s₀ m).len ≤ (spR s₀).len := ⟨rfl, by show min m (SL s₀) + (SL s₀ - m) ≤ SL s₀; omega⟩

theorem srcM_sub {s₀ : State} (hT : SPre s₀) (m : Nat) : Region.Sub (srcM s₀ m) (spR s₀) :=
  Offset.sub_base _ (by have := hT.wrap_s; show min m (SL s₀) + (SL s₀ - m) ≤ SL s₀; omega)

theorem srcM_wrap {s₀ : State} (hT : SPre s₀) (m : Nat) :
    (sp s₀ + BitVec.ofNat 64 (min m (SL s₀))).toNat + (SL s₀ - m) ≤ 2 ^ 64 := by
  have hw := hT.wrap_s
  have hs := (sp s₀ + BitVec.ofNat 64 (min m (SL s₀))).isLt
  have hSL : SL s₀ < 2 ^ 64 := (stackArg s₀ 3).isLt
  by_cases h2 : (sp s₀).toNat + min m (SL s₀) < 2 ^ 64
  · rw [BitVec.toNat_add, toNat_ofNat_lt (show min m (SL s₀) < 2 ^ 64 by omega), Nat.mod_eq_of_lt h2]; omega
  · omega

/-- The inline code's precondition, its permissions narrowed to its regions. -/
theorem SArgs.pre {s₀ : State} (hT : SPre s₀) {m : Nat} (hm : m ≤ L s₀) {s : State} (h : SArgs s₀ m s)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) :
    Proof.ChaCha20.xorSplitX86_64.pre (s.withRegions [srcM s₀ m] (wrM s₀ m)) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hSL : SL s₀ < 2 ^ 64 := (stackArg s₀ 3).isLt
  have eL : (BitVec.ofNat 64 (L s₀ - m)).toNat = L s₀ - m := toNat_ofNat_lt (by simp only [L]; omega)
  have eS : (BitVec.ofNat 64 (SL s₀ - m)).toNat = SL s₀ - m := toNat_ofNat_lt (by omega)
  have sm := srcM_sub hT m
  have dm := dRm_sub s₀ hm
  have c64 := sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)
  have c128 := sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)
  simp only [Proof.ChaCha20.xorSplitX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hrsp, eL, eS]
  refine ⟨trivial, trivial, by have := hT.le; omega,
    (hp.c_d.sub_left c64).sub_right dm,
    sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega),
    ((hp.c_d.symm.sub_right c128).sub_left dm),
    (hT.s_c.sub_left sm).sub_right c64, (hT.s_d.sub_left sm).sub_right dm, (hT.s_c.sub_left sm).sub_right c128,
    hp.ret_c.sub_right c64, hp.ret_d.sub_right dm, hp.ret_c.sub_right c128,
    hp.stk_c.sub_right c64, hp.stk_d.sub_right dm, hp.stk_c.sub_right c128,
    srcM_wrap hT m, ?_⟩
  simpa only [dRm] using hp.wrap_dm hm

/-- The inline code's writable regions are within the state's. -/
theorem SArgs.hw {s₀ : State} (hT : SPre s₀) {m : Nat} (hm : m ≤ L s₀) {s : State} (hwr : s.wr = s₀.wr) :
    Covers (wrM s₀ m) s.wr := by
  have hp := hT.hp
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega_using []⟩
  · exact ⟨dR s₀, by rw [hwr]; exact hp.d_wr, m, by simp [off_eq], by show m + (L s₀ - m) ≤ L s₀; omega_using [hm]⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega_using []⟩

/-- The inline code's regions are within the state's. -/
theorem SArgs.hc {s₀ : State} (hT : SPre s₀) {m : Nat} (hm : m ≤ L s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : Covers ([srcM s₀ m] ++ wrM s₀ m) (s.rd ++ s.wr) := by
  refine Covers.append_left ?_ (Covers.right (SArgs.hw hT hm hwr))
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨spR s₀, List.mem_append_left _ (by rw [hrd]; exact hT.s_rd), _, srcM_in s₀ m⟩

/-- The inline code of `vg_chacha20_xor_split_avx512`, from its arguments:
its postcondition, in memory changed only within its regions and the stack
below `rsp` that `seal`'s calls take. -/
theorem SArgs.inline {s₀ : State} (hT : SPre s₀) {m : Nat} (hm : m ≤ L s₀) {s : State} (h : SArgs s₀ m s)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' →
      Frame (wrM s₀ m ++ [stkR s₀]) s.mem s'.mem →
      bytesAt s'.mem (off (dp s₀) m) (L s₀ - m) =
        List.zipWith (· ^^^ ·)
          (bytesAt s.mem (sp s₀ + BitVec.ofNat 64 (min m (SL s₀))) (SL s₀ - m) ++
            (bytesAt s.mem (off (dp s₀) m) (L s₀ - m)).drop (SL s₀ - m))
          (keystream (stateAt s.mem (off (cx s₀) 64)) (L s₀ - m)) → Q s') :
    WP isa Impl.ChaCha20.X86_64.Avx512.xorSplit s Q := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hSL : SL s₀ < 2 ^ 64 := (stackArg s₀ 3).isLt
  have eL : (BitVec.ofNat 64 (L s₀ - m)).toNat = L s₀ - m := toNat_ofNat_lt (by simp only [L]; omega)
  have eS : (BitVec.ofNat 64 (SL s₀ - m)).toNat = SL s₀ - m := toNat_ofNat_lt (by omega)
  have hd := xorSplit_depth
  have hw := SArgs.hw hT hm hwr
  have hc := SArgs.hc hT hm hrd hwr
  refine WP.inlineSp Proof.ChaCha20.X86_64.Avx512Split.xorSplit_correct xorSplit_nosp (by omega)
    (h.pre hT hm hrsp) hc hw fun s' rd' wr' abi f _ post => hQ s' rd' wr' abi ?_ ?_
  · refine f.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨stkR s₀, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hrsp]; exact below_sub (by omega) (by lit_omega)
  · simp only [Proof.ChaCha20.xorSplitX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi,
      h.rdx, h.rcx, h.r8, eL, eS] at post
    exact post

/-! ## The data after its first `mm` bytes -/

theorem bytesAt_eq_zip {m : Mem} {p : Addr} {n : Nat} {xs ks : List Byte} (hx : xs.length = n)
    (hk : ks.length = n) (h : ∀ k < n, m (p + BitVec.ofNat 64 k) = xs.getD k 0 ^^^ ks.getD k 0) :
    bytesAt m p n = List.zipWith (· ^^^ ·) xs ks := by
  apply List.ext_getElem (by simp [bytesAt, hx, hk])
  intro k h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith, h k h₁]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem zip_get {m : Mem} {p : Addr} {n : Nat} {xs ks : List Byte} (hx : xs.length = n)
    (hks : ks.length = n) (h : bytesAt m p n = List.zipWith (· ^^^ ·) xs ks) {k : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = xs.getD k 0 ^^^ ks.getD k 0 := by
  have hk1 : k < (bytesAt m p n).length := by simp [bytesAt, hk]
  have e := List.getElem_of_eq h hk1
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith] at e
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem bytesAt_getD (m : Mem) (p : Addr) {n j : Nat} (hj : j < n) :
    (bytesAt m p n).getD j 0 = m (p + BitVec.ofNat 64 j) := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

/-- A byte of `src`'s bytes followed by the data's after them. -/
theorem getD_split {A B : List Byte} {d j : Nat} (hA : A.length = d) :
    (A ++ B.drop d).getD j 0 = if j < d then A.getD j 0 else B.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega), hA, List.getElem?_drop, show d + (j - d) = j by omega]

/-- After `PTs` is encrypted, before the keystream is wiped. -/
structure CryptedS (s₀ s : State) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (PTs s₀ s.mem)

theorem cryptBigSplit_ok {s₀ : State} (hT : SPre s₀) {s : State} (h : Inv s₀ s) (hbig : ¬ L s₀ ≤ 960)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mm s₀, s.mem (off (cx s₀) (736 + k)) =
      (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa cryptBigSplit s (CryptedS s₀ s) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hSL : SL s₀ < 2 ^ 64 := (stackArg s₀ 3).isLt
  have hM : mm s₀ ≤ 960 := mOf_le 960 1024 (L s₀)
  have hML : mm s₀ ≤ L s₀ := mOf_le_len 960 1024 (L s₀)
  have hdvd : 64 ∣ mm s₀ := by rw [mm, mOf_big hbig]; exact splitOf_dvd (.inr (.inl rfl)) _
  refine WP.seq (WP.mono (cryptPre_ok Proof.ChaCha20.X86_64.XorImpl.avx512 (pass_of _) hp h)
    fun s₁ ⟨a₁, cs₁, rd₁, mx, fx, dx, m₁⟩ => ?_)
  change XArgsM s₀ (mm s₀) s₁ at a₁
  change Frame [⟨dp s₀, mm s₀⟩] s.mem mx at fx
  change ∀ k < mm s₀, _ at dx
  change s₁.mem = mx.writeW (off (cx s₀) 112) (BitVec.ofNat 32 (mm s₀ / 64 + 1)) at m₁
  have fw : Frame [sub s₀ 64 64] mx s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have dpre : ∀ r ∈ [(⟨dp s₀, mm s₀⟩ : Region)], (sub s₀ 64 64).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hML)
  have hpre : ∀ r ∈ [(⟨dp s₀, mm s₀⟩ : Region)], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_d.sub_right (Region.sub_prefix hML)
  have harg : ∀ r ∈ [sub s₀ 64 64], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_c.sub_right (sub_ctx s₀ (by lit_omega))
  have st₁ : stateAt s₁.mem (off (cx s₀) 64) =
      VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (mm s₀ / 64) := by
    rw [m₁, stateAt_ctrW, stateAt_frame fx dpre, hst, set12_ctr]
  refine WP.seq (WP.mono (splitArgs_ok hT a₁ (by rw [rd₁, h.rd])
    (by rw [arg_frame (.inl rfl) fw harg, arg_frame (.inl rfl) fx hpre, hS2])
    (by rw [arg_frame (.inr rfl) fw harg, arg_frame (.inr rfl) fx hpre, hS3]))
    fun s₂ ⟨sa₂, cs₂, rd₂, wr₂, m₂⟩ => ?_)
  refine WP.seq (sa₂.inline hT hML (by rw [cs₂ _ calleeSaved_rsp, a₁.rsp]) (by rw [rd₂, rd₁, h.rd])
    (by rw [wr₂, a₁.wr]) fun s₃ rd₃ wr₃ abi₃ f₃ data₃ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r := fun r hr => abi₃.1 r hr
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₃) fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ => ?_
  have r15 : s₃.gpr .r15 = cx s₀ := by
    rw [cs₃ _ (by simp [calleeSaved]), cs₂ _ (by simp [calleeSaved]), cs₁ _ (by simp [calleeSaved]), h.r15]
  -- A byte of the data is in none of the regions but the data's.
  have nctx : ∀ {k a n : Nat}, k < L s₀ → a + n ≤ 1696 → ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk ha hc => hp.c_d _ (sub_ctx s₀ ha _ hc) (byte_dR hk)
  have nstk : ∀ {k : Nat}, k < L s₀ → ¬ (stkR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk hc => hp.stk_d _ hc (byte_dR hk)
  have m₂s : s₂.mem = s₁.mem := m₂
  refine ⟨by rw [e4, r15, off_eq], fun r hr h15 => ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, a₁.wr, h.wr],
    ?_, ?_⟩
  · have hrsi : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₄ r hrsi, cs₃ r hr, cs₂ r hr, cs₁ r hr]
  · rw [m₄]
    have f₂₃ : Frame (wrM s₀ (mm s₀) ++ [stkR s₀]) s₁.mem s₃.mem := m₂s ▸ f₃
    refine (fx.sub fun r hr => ?_).trans ((fw.sub fun r hr => ?_).trans (f₂₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, Region.sub_prefix hML⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [wrM, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, dRm_sub s₀ hML⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [encrypt_eq, length_PTs, m₄]
    apply bytesAt_eq_zip (length_PTs _ _) (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [PTs_getD _ hk]
    have m₁k : ∀ {x : Addr}, ¬ (sub s₀ 64 64).Contains x 1 → s₁.mem x = mx x :=
      fun hx => fw _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx
    -- `src`'s bytes, as on entry.
    have src_k : ∀ {j : Nat}, j < SL s₀ → s₁.mem (sp s₀ + BitVec.ofNat 64 j) = s.mem (sp s₀ + BitVec.ofNat 64 j) :=
      fun hj => by
        rw [m₁k (hT.nctx hj (by lit_omega)), fx _ fun r hr => ?_]
        simp only [List.mem_singleton] at hr; subst hr
        exact fun hc => hT.ndR hj (Region.sub_prefix hML _ hc)
    by_cases hkm : k < mm s₀
    · rw [ite_eq_right (fun h => by omega), f₃ _ fun r hr => ?_, m₂s, m₁k (nctx hk (by lit_omega)), dx k hkm, hks k hkm]
      simp only [wrM, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact nctx hk (by lit_omega)
      · exact fun hc => Offset.disjoint (dp s₀) (d := k) (n := 1) (e := mm s₀) (k := L s₀ - mm s₀)
          (Or.inl (by omega)) (by simp only [L] at hk; omega) (by simp only [L] at hML ⊢; omega) _
          (Region.contains_self _ _) (by simpa only [dRm, off_eq] using hc)
      · exact nctx hk (by lit_omega)
      · exact nstk hk
    · have hj : k - mm s₀ < L s₀ - mm s₀ := by omega
      have hle := hT.le
      have e₃ := zip_get (by simp only [List.length_append, List.length_drop, VG.Proof.Poly1305.length_bytesAt]; omega)
        (VG.Proof.ChaCha20.length_keystream _ _) data₃ hj
      have ea : off (dp s₀) (mm s₀) + BitVec.ofNat 64 (k - mm s₀) = dp s₀ + BitVec.ofNat 64 k := by
        rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      rw [ea, getD_split (VG.Proof.Poly1305.length_bytesAt _ _ _),
        m₂s, st₁] at e₃
      have ks : (keystream (VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (mm s₀ / 64))
          (L s₀ - mm s₀)).getD (k - mm s₀) 0 =
          (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0 := by
        obtain ⟨a, ha⟩ := hdvd
        rw [ha, Nat.mul_div_cancel_left _ (by decide), keystream_skip _ (by omega) hk]
      rw [e₃, ks]
      refine congrArg (· ^^^ _) ?_
      by_cases hks' : k < SL s₀
      · have hmS : min (mm s₀) (SL s₀) = mm s₀ := Nat.min_eq_left (by omega)
        rw [ite_eq_left (show k - mm s₀ < SL s₀ - mm s₀ by omega), ite_eq_left (show mm s₀ ≤ k ∧ k < SL s₀ from ⟨by omega, hks'⟩)]
        rw [bytesAt_getD _ _ (show k - mm s₀ < SL s₀ - mm s₀ by omega), hmS, BitVec.add_assoc, ← BitVec.ofNat_add,
          Nat.add_sub_cancel' (by omega), src_k hks']
      · rw [ite_eq_right (show ¬ (k - mm s₀ < SL s₀ - mm s₀) by omega),
          ite_eq_right (show ¬ (mm s₀ ≤ k ∧ k < SL s₀) by omega)]
        rw [bytesAt_getD _ _ hj, ea, m₁k (nctx hk (by lit_omega)), fx _ fun r hr => ?_]
        simp only [List.mem_singleton] at hr; subst hr
        exact fun hc => Offset.disjoint_base (dp s₀) (d := k) (n := 1) (by omega)
          (by simp only [L] at hk; omega) _ (Region.contains_self _ _) hc

/-! ## The data encrypted, and the keystream wiped -/

/-- `crypt_ok`, for `cryptSplit`: `PTs` encrypted. -/
theorem cryptSplit_ok {s₀ : State} (hT : SPre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mm s₀, s.mem (off (cx s₀) (736 + k)) =
      (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa cryptSplit s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 64 384, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (PTs s₀ s.mem) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hm : mm s₀ ≤ 960 := mOf_le 960 1024 (L s₀)
  unfold cryptSplit
  refine WP.seq (WP.mono (cmpFold_ok (fold := 960) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := CryptedS s₀ s₁) ?_ fun s₂ c₂ => ?_)
  · refine WP.ite (decide (L s₀ < 960 + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      refine WP.mono (cryptSmall_ok (fold := 960) (pass := 1024) (by lit_omega) (.inr (.inr rfl)) hp h₁
        (by omega_using [hc]) (by rw [m₁]; exact hks)) fun s' c => ⟨c.rsi, c.cs, c.rd, c.wr, c.frame, ?_⟩
      rw [PTs_small (by omega_using [hc])]; exact c.data
    · simp only [decide_eq_false_iff_not] at hc
      exact cryptBigSplit_ok hT h₁ (by omega_using [hc]) (by rw [m₁]; exact hst) (by rw [m₁]; exact hks)
        (by rw [m₁]; exact hS2) (by rw [m₁]; exact hS3)
  refine WP.seq (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ r h15, c₂.cs r hr h15, g₁]
  have i₃ : Inv s₀ s₃ := h.step cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁])
    (by rw [m₃, ← m₁]; exact c₂.frame) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  -- The keystream wiped.
  refine WP.seq (WP.mono (foldM_ok (fold := 960) (pass := 1024) (len := L s₀) (by lit_omega) (.inr (.inl rfl)) hL9
    (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (add64_ok (n := mm s₀) d₄) fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ => ?_)
  refine WP.mono (zeroKs_ok (w := 6) (.inr (.inr rfl)) hp (n := 64 + mm s₀) (by omega_using []) (by lit_omega) d₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ => ?_
  have cs₆ : ∀ r ∈ calleeSaved, s₆.gpr r = s₃.gpr r := fun r hr => by
    have h' := calleeSaved_ne hr
    rw [g₆ r h'.1 h'.2.1, g₅ r h'.2.2.1, g₄ r h'.2.2.1]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  refine ⟨i₃.step cs₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    fun r hr => by rw [cs₆ r hr, cs₃ r hr], ?_, ?_⟩
  · have fc : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₃.mem := by rw [m₃, ← m₁]; exact c₂.frame
    refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt hL9), m₃, c₂.data, ← m₁]

end VG.Proof.ChaCha20Poly1305.X86_64.Split
