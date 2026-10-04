import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.ChaCha20.X86.Quad
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 block function on x86 (32-bit), with SSE2: the rounds

Doubleword `i` of `xmm r` holds word `4 r + i` of the state. A quarter round
on each doubleword (`vqr`) is the column round; with the rows rotated
(`diag`), it is the diagonal round.
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-! ## The column and diagonal rounds, a column or diagonal at a time -/

/-- The column round. -/
abbrev colRound (v : CState) : CState :=
  qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15

/-- The diagonal round. -/
abbrev diagRound (v : CState) : CState :=
  qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

theorem fin16_val (n : Nat) : ((no_index (OfNat.ofNat n) : Fin 16) : Nat) = n % 16 := rfl

theorem innerBlock_eq (v : CState) : innerBlock v = diagRound (colRound v) := rfl

/-- Column `i` of the column round is the quarter round on column `i`. -/
theorem col_get (v : CState) {i : Nat} (hi : i < 4) :
    (colRound v)[i] = (quarterRound v[i] v[4 + i] v[8 + i] v[12 + i]).1 ∧
    (colRound v)[4 + i] = (quarterRound v[i] v[4 + i] v[8 + i] v[12 + i]).2.1 ∧
    (colRound v)[8 + i] = (quarterRound v[i] v[4 + i] v[8 + i] v[12 + i]).2.2.1 ∧
    (colRound v)[12 + i] = (quarterRound v[i] v[4 + i] v[8 + i] v[12 + i]).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp only [qround_get, Fin.getElem_fin, fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-- Diagonal `i` of the diagonal round is the quarter round on diagonal `i`. -/
theorem diag_get (v : CState) {i : Nat} (hi : i < 4) :
    (diagRound v)[i] =
      (quarterRound v[i] v[4 + (i + 1) % 4] v[8 + (i + 2) % 4] v[12 + (i + 3) % 4]).1 ∧
    (diagRound v)[4 + (i + 1) % 4] =
      (quarterRound v[i] v[4 + (i + 1) % 4] v[8 + (i + 2) % 4] v[12 + (i + 3) % 4]).2.1 ∧
    (diagRound v)[8 + (i + 2) % 4] =
      (quarterRound v[i] v[4 + (i + 1) % 4] v[8 + (i + 2) % 4] v[12 + (i + 3) % 4]).2.2.1 ∧
    (diagRound v)[12 + (i + 3) % 4] =
      (quarterRound v[i] v[4 + (i + 1) % 4] v[8 + (i + 2) % 4] v[12 + (i + 3) % 4]).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp only [qround_get, Fin.getElem_fin, fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## The rows in the registers -/

/-- The state `v` is in `xmm0, …, xmm3`: word `4 r + i` in doubleword `i` of `xmm r`. -/
structure Rows (v : CState) (s : State) : Prop where
  r0 : ∀ i (hi : i < 4), dw s .xmm0 i = v[i]
  r1 : ∀ i (hi : i < 4), dw s .xmm1 i = v[4 + i]
  r2 : ∀ i (hi : i < 4), dw s .xmm2 i = v[8 + i]
  r3 : ∀ i (hi : i < 4), dw s .xmm3 i = v[12 + i]

theorem shuf39 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x39) i = dword x ((i + 1) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf4e (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x4e) i = dword x ((i + 2) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf93 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x93) i = dword x ((i + 3) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

/-- `xmm1, xmm2, xmm3` rotated by `a, b, c` doublewords by three `pshufd`. -/
theorem shufs_ok (o₁ o₂ o₃ : BitVec 8) {a b c : Nat}
    (h₁ : ∀ x i, i < 4 → dword (shufDwords x o₁) i = dword x ((i + a) % 4))
    (h₂ : ∀ x i, i < 4 → dword (shufDwords x o₂) i = dword x ((i + b) % 4))
    (h₃ : ∀ x i, i < 4 → dword (shufDwords x o₃) i = dword x ((i + c) % 4)) (s : State) :
    WP isa (.block [.xop (.pshufd .xmm1 .xmm1 o₁), .xop (.pshufd .xmm2 .xmm2 o₂),
      .xop (.pshufd .xmm3 .xmm3 o₃)]) s fun s' =>
      (∀ i, i < 4 → dw s' .xmm0 i = dw s .xmm0 i) ∧
      (∀ i, i < 4 → dw s' .xmm1 i = dw s .xmm1 ((i + a) % 4)) ∧
      (∀ i, i < 4 → dw s' .xmm2 i = dw s .xmm2 ((i + b) % 4)) ∧
      (∀ i, i < 4 → dw s' .xmm3 i = dw s .xmm3 ((i + c) % 4)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun i _ => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, trivial, trivial, trivial,
    trivial⟩ <;>
    simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]
  · exact h₁ _ i hi
  · exact h₂ _ i hi
  · exact h₃ _ i hi

theorem diag_eq : diag = [.xop (.pshufd .xmm1 .xmm1 0x39), .xop (.pshufd .xmm2 .xmm2 0x4e),
    .xop (.pshufd .xmm3 .xmm3 0x93)] := rfl
theorem undiag_eq : undiag = [.xop (.pshufd .xmm1 .xmm1 0x93), .xop (.pshufd .xmm2 .xmm2 0x4e),
    .xop (.pshufd .xmm3 .xmm3 0x39)] := rfl

theorem vqr_rows {v : CState} {s : State} (h : Rows v s) :
    WP isa (.block vqr) s fun s' => Rows (colRound v) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (vqr_ok s) fun _ ⟨q, _, g, m, r, w⟩ => by
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, g, m, r, w⟩ <;>
    obtain ⟨a, b, c, d⟩ := q i hi <;>
    rw [h.r0 i hi, h.r1 i hi, h.r2 i hi, h.r3 i hi] at a b c d
    · rw [a, (col_get v hi).1]
    · rw [b, (col_get v hi).2.1]
    · rw [c, (col_get v hi).2.2.1]
    · rw [d, (col_get v hi).2.2.2]

theorem doubleRound_ok {v : CState} {s : State} (h : Rows v s) :
    WP isa doubleRound s fun s' => Rows (innerBlock v) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold doubleRound
  rw [WP.block_append_iff]
  refine WP.mono (vqr_rows h) fun s₁ ⟨h₁, g₁, m₁, r₁, w₁⟩ => ?_
  rw [WP.block_append_iff, diag_eq]
  refine WP.mono (shufs_ok 0x39 0x4e 0x93 (a := 1) (b := 2) (c := 3) (fun x i hi => shuf39 x hi)
    (fun x i hi => shuf4e x hi) (fun x i hi => shuf93 x hi) s₁)
    fun s₂ ⟨d0, d1, d2, d3, g₂, m₂, r₂, w₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vqr_ok s₂) fun s₃ ⟨q, _, g₃, m₃, r₃, w₃⟩ => ?_
  rw [undiag_eq]
  refine WP.mono (shufs_ok 0x93 0x4e 0x39 (a := 3) (b := 2) (c := 1) (fun x i hi => shuf93 x hi)
    (fun x i hi => shuf4e x hi) (fun x i hi => shuf39 x hi) s₃)
    fun s₄ ⟨u0, u1, u2, u3, g₄, m₄, r₄, w₄⟩ => ?_
  rw [innerBlock_eq]
  -- Lane `i` of the second quarter round: diagonal `i`.
  have lane : ∀ i (hi : i < 4),
      dw s₂ .xmm0 i = (colRound v)[i] ∧ dw s₂ .xmm1 i = (colRound v)[4 + (i + 1) % 4] ∧
      dw s₂ .xmm2 i = (colRound v)[8 + (i + 2) % 4] ∧ dw s₂ .xmm3 i = (colRound v)[12 + (i + 3) % 4] :=
    fun i hi => ⟨(d0 i hi).trans (h₁.r0 i hi), (d1 i hi).trans (h₁.r1 _ (Nat.mod_lt _ (by decide))),
      (d2 i hi).trans (h₁.r2 _ (Nat.mod_lt _ (by decide))),
      (d3 i hi).trans (h₁.r3 _ (Nat.mod_lt _ (by decide)))⟩
  have hq : ∀ i (hi : i < 4),
      dw s₃ .xmm0 i = (diagRound (colRound v))[i] ∧
      dw s₃ .xmm1 i = (diagRound (colRound v))[4 + (i + 1) % 4] ∧
      dw s₃ .xmm2 i = (diagRound (colRound v))[8 + (i + 2) % 4] ∧
      dw s₃ .xmm3 i = (diagRound (colRound v))[12 + (i + 3) % 4] := fun i hi => by
    obtain ⟨a, b, c, d⟩ := q i hi
    obtain ⟨l0, l1, l2, l3⟩ := lane i hi
    obtain ⟨e0, e1, e2, e3⟩ := diag_get (colRound v) hi
    rw [l0, l1, l2, l3] at a b c d
    exact ⟨a.trans e0.symm, b.trans e1.symm, c.trans e2.symm, d.trans e3.symm⟩
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩,
    by rw [g₄, g₃, g₂, g₁], by rw [m₄, m₃, m₂, m₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [u0 i hi]; exact (hq i hi).1
  · rw [u1 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.1]
    exact getElem_congr_idx (by omega)
  · rw [u2 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.1]
    exact getElem_congr_idx (by omega)
  · rw [u3 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.2]
    exact getElem_congr_idx (by omega)

theorem rounds_ok {v : CState} {s₀ : State} (h : Rows v s₀) :
    ∀ n, WP isa (rounds n) s₀ fun s => Rows (Nat.repeat innerBlock n v) s ∧
      s.gpr = s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ ⟨h₁, g₁, m₁, r₁, w₁⟩ =>
      WP.mono (doubleRound_ok h₁) fun _ ⟨h₂, g₂, m₂, r₂, w₂⟩ =>
        ⟨h₂, g₂.trans g₁, m₂.trans m₁, r₂.trans r₁, w₂.trans w₁⟩)

end VG.Proof.ChaCha20.X86

/-!
# ChaCha20 block function on x86 (32-bit): the whole function
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open VG.X86 in
/-- X86 (32-bit) contract for `vg_chacha20_block(state: *const [u32; 16], buf:
*mut [u32; 64])`, whose arguments are on the stack (cdecl): writes `block` of
the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read the two arguments (8 bytes above the return address) and `state` (64
bytes), and read and write `buf` (256 bytes; its first 64 bytes hold the
result on exit, and the rest is scratch space whose contents on exit are
unspecified). `buf` may not overlap `state`, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers) are public; the state (key, counter
and nonce) is secret. -/
def blockX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let buf : Region := ⟨(arg s 1).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [state, args] ∧ s.wr = [buf] ∧
    buf.Disjoint state ∧ args.Disjoint buf ∧ ret.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 1).setWidth 64) = block (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- The two pointers. -/
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
/-- Their 64-bit addresses. -/
abbrev SA : Addr := (st s₀).setWidth 64
abbrev BA : Addr := (bp s₀).setWidth 64
abbrev stR : Region := ⟨SA s₀, 64⟩
abbrev bufR : Region := ⟨BA s₀, 256⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀, argR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  arg_buf : (argR s₀).Disjoint (bufR s₀)
  ret_buf : (retR s₀).Disjoint (bufR s₀)
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (bp s₀).toNat + 256 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by lit_omega)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem eaB {d : Nat} (hd : d < 256) : addr (bp s₀) d = BA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.buf_fits; omega)

theorem eaS {d : Nat} (hd : d < 64) : addr (st s₀) d = SA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem eaA {d : Nat} (hd : d < 12) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem hw : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 2) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  simp only [argR, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    hp.eaA (by lit_omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, hp.eaA (by lit_omega)]
  exact Offset.sub _ (by lit_omega) (by lit_omega)

theorem arg_contains {i : Nat} (hi : i < 2) : (argR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [argR]
  rw [show argAddr s₀ i = addr (esp₀ s₀) (4 + 4 * i) from rfl, hp.eaA (by lit_omega),
    show argAddr s₀ 0 = addr (esp₀ s₀) 4 from rfl, hp.eaA (by lit_omega)]
  exact contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 2) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨argR s₀, by simp [hp.rd], hp.arg_contains hi⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by lit_omega) (by lit_omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre


theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-- The result, `buf[0..64)`. -/
abbrev workR (B : Addr) : Region := ⟨B, 64⟩

/-! ## Loading the state -/

theorem load_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block load) s₀ fun s =>
      Rows (V s₀) s ∧ s.gpr .eax = st s₀ ∧ s.gpr .ecx = bp s₀ ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧
      s.wr = s₀.wr := by
  unfold load
  refine Wp.wp_ldm rfl (hp.in_arg (i := 0) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.in_arg (i := 1) (by decide))
    fun s₂ u₂ => ?_
  have heax : s₂.gpr .eax = st s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  have e : ∀ d, d < 64 → s₂.ea (at_ .eax d) = SA s₀ + BitVec.ofNat 64 d := fun d hd => by
    show addr (s₂.gpr .eax) d = _; rw [heax]; exact hp.eaS hd
  have i : ∀ d, d + 16 ≤ 64 → InRegions (s₂.rd ++ s₂.wr) (SA s₀ + BitVec.ofNat 64 d) 16 := fun d hd => by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    exact ⟨stR s₀, by simp [hp.rd], contains_off hd (by lit_omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, Quad.ea_setXmm,
    e 0 (by decide), e 16 (by decide), e 32 (by decide), e 48 (by decide), i 0 (by decide),
    i 16 (by decide), i 32 (by decide), i 48 (by decide), ite_true, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq,
    exists_eq_left']
  have hm : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, heax,
    by rw [u₂.gpr, u₁.mem]; rfl, fun r h₁ h₂ => by rw [u₂.other r h₂, u₁.other r h₁], hm,
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩ <;>
    simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]
  · have := Quad.row_lane s₀.mem (SA s₀) (r := 0) (by decide) hi
    simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [hm]; exact this
  · rw [hm]; exact Quad.row_lane s₀.mem (SA s₀) (r := 1) (by decide) hi
  · rw [hm]; exact Quad.row_lane s₀.mem (SA s₀) (r := 2) (by decide) hi
  · rw [hm]; exact Quad.row_lane s₀.mem (SA s₀) (r := 3) (by decide) hi

/-! ## Adding the input state and storing the result -/

theorem addRow_ok {s₀ : State} (hp : Pre s₀) {x : XReg} (hx : x ≠ .xmm4) {r : Nat} (hr : r < 4)
    {s : State} (heax : s.gpr .eax = st s₀) (hecx : s.gpr .ecx = bp s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame [workR (BA s₀)] s₀.mem s.mem) :
    WP isa (.block (addRow x r)) s fun s' =>
      (∀ i (hi : i < 4), s'.mem.readW (BA s₀ + BitVec.ofNat 64 (16 * r + 4 * i)) 32 =
        dw s x i + (V s₀)[4 * r + i]) ∧
      (∀ d, d + 4 ≤ 64 → d + 4 ≤ 16 * r ∨ 16 * r + 16 ≤ d →
        s'.mem.readW (BA s₀ + BitVec.ofNat 64 d) 32 = s.mem.readW (BA s₀ + BitVec.ofNat 64 d) 32) ∧
      Frame [workR (BA s₀)] s.mem s'.mem ∧ (∀ y, y ≠ x → y ≠ .xmm4 → s'.xmm y = s.xmm y) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have eS : s.ea (at_ .eax (16 * r)) = SA s₀ + BitVec.ofNat 64 (16 * r) := by
    show addr (s.gpr .eax) _ = _; rw [heax]; exact hp.eaS (d := 16 * r) (by omega)
  have eB : s.ea (at_ .ecx (16 * r)) = BA s₀ + BitVec.ofNat 64 (16 * r) := by
    show addr (s.gpr .ecx) _ = _; rw [hecx]; exact hp.eaB (d := 16 * r) (by omega)
  have iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hrd, hwr]; exact ⟨stR s₀, by simp [hp.rd], contains_off (by omega) (by lit_omega)⟩
  have oB : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hwr]; exact hp.out_buf (by omega)
  have hS : s.mem.readW (SA s₀ + BitVec.ofNat 64 (16 * r)) 128 =
      s₀.mem.readW (SA s₀ + BitVec.ofNat 64 (16 * r)) 128 :=
    hf.readW (r := stR s₀) (contains_off (by omega) (by lit_omega))
      (by simpa using hp.buf_st.symm.sub_right (Region.sub_prefix (by decide))) (by decide)
  apply WP.of_runBlock
  simp only [addRow, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, Quad.ea_setXmm, eS, eB, iS, RegUpd.wr_setXmm, oB, ite_true, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun d hd hd' => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_off (by omega) (by lit_omega)), fun y h₁ h₂ => ?_, trivial, trivial, trivial⟩
  · rw [Quad.lane_write_self _ _ _ _ hi, RegUpd.xmm_setXmm_self, dword_paddd _ _ hi,
      RegUpd.xmm_setXmm_of_ne _ _ hx, RegUpd.xmm_setXmm_self, hS, Quad.row_lane _ _ hr hi]
  · exact Quad.lane_write_other _ _ _ (by omega) (by omega) hd'
  · rw [RegUpd.xmm_setXmm_of_ne _ _ h₁, RegUpd.xmm_setXmm_of_ne _ _ h₂]

theorem finish_eq : finish = addRow .xmm0 0 ++ (addRow .xmm1 1 ++ (addRow .xmm2 2 ++ addRow .xmm3 3)) := by
  simp only [finish, List.append_assoc]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' => abiPreserved s₀ s' ∧ Proof.ChaCha20.blockX86.post s₀ s' := by
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨h₁, ea₁, ec₁, k₁, m₁, r₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok h₁ 10) fun s₂ ⟨h₂, g₂, m₂, r₂, w₂⟩ => ?_)
  have f₂ : Frame [workR (BA s₀)] s₀.mem s₂.mem := by rw [m₂, m₁]; exact Frame.refl _ _
  have ga : ∀ (t : State), t.gpr = s₂.gpr → t.gpr .eax = st s₀ ∧ t.gpr .ecx = bp s₀ := fun t g =>
    ⟨by rw [g, g₂, ea₁], by rw [g, g₂, ec₁]⟩
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (addRow_ok hp (x := .xmm0) (by decide) (r := 0) (by decide) (ga s₂ rfl).1 (ga s₂ rfl).2
    (by rw [r₂, r₁]) (by rw [w₂, w₁]) f₂) fun s₃ ⟨a₃, o₃, f₃, x₃, g₃, r₃, w₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addRow_ok hp (x := .xmm1) (by decide) (r := 1) (by decide) (ga s₃ g₃).1 (ga s₃ g₃).2
    (by rw [r₃, r₂, r₁]) (by rw [w₃, w₂, w₁]) (f₂.trans f₃)) fun s₄ ⟨a₄, o₄, f₄, x₄, g₄, r₄, w₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addRow_ok hp (x := .xmm2) (by decide) (r := 2) (by decide) (ga s₄ (g₄.trans g₃)).1
    (ga s₄ (g₄.trans g₃)).2 (by rw [r₄, r₃, r₂, r₁]) (by rw [w₄, w₃, w₂, w₁]) ((f₂.trans f₃).trans f₄))
    fun s₅ ⟨a₅, o₅, f₅, x₅, g₅, r₅, w₅⟩ => ?_
  refine WP.mono (addRow_ok hp (x := .xmm3) (by decide) (r := 3) (by decide)
    (ga s₅ ((g₅.trans g₄).trans g₃)).1 (ga s₅ ((g₅.trans g₄).trans g₃)).2 (by rw [r₅, r₄, r₃, r₂, r₁])
    (by rw [w₅, w₄, w₃, w₂, w₁]) (((f₂.trans f₃).trans f₄).trans f₅))
    fun s₆ ⟨a₆, o₆, f₆, _, g₆, _, _⟩ => ?_
  have hF : Frame [workR (BA s₀)] s₀.mem s₆.mem := (((f₂.trans f₃).trans f₄).trans f₅).trans f₆
  have hg : s₆.gpr = s₂.gpr := ((g₆.trans g₅).trans g₄).trans g₃
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hg, g₂, k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  · refine hF.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simpa using hp.ret_buf.sub_right (Region.sub_prefix (by decide))
  · show stateAt s₆.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
    apply Vector.ext
    intro k hk
    rw [show (stateAt s₆.mem (BA s₀))[k] = s₆.mem.readW (BA s₀ + BitVec.ofNat 64 (4 * k)) 32 by
      simp only [stateAt, Vector.getElem_ofFn], Spec.ChaCha20.block, Vector.getElem_zipWith]
    have x₂ : ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → y ≠ .xmm2 → y ≠ .xmm4 → s₅.xmm y = s₂.xmm y :=
      fun y h0 h1 h2 h4 => by rw [x₅ y h2 h4, x₄ y h1 h4, x₃ y h0 h4]
    rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
    · have a := a₃ k h
      simp only [Nat.mul_zero, Nat.zero_add] at a
      rw [show 4 * k = 0 + 4 * k by omega, o₆ _ (by omega) (by omega), o₅ _ (by omega) (by omega),
        o₄ _ (by omega) (by omega), Nat.zero_add, a, h₂.r0 k h]
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k = 4 + i := ⟨k - 4, by omega, by omega⟩
      have a := a₄ i hi
      simp only [Nat.reduceMul] at a
      rw [show 4 * (4 + i) = 16 + 4 * i by omega, o₆ _ (by omega) (by omega),
        o₅ _ (by omega) (by omega), a, show dw s₃ .xmm1 i = dw s₂ .xmm1 i by
          simp only [dw]; rw [x₃ _ (by decide) (by decide)], h₂.r1 i hi]
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k = 8 + i := ⟨k - 8, by omega, by omega⟩
      have a := a₅ i hi
      simp only [Nat.reduceMul] at a
      rw [show 4 * (8 + i) = 32 + 4 * i by omega, o₆ _ (by omega) (by omega), a,
        show dw s₄ .xmm2 i = dw s₂ .xmm2 i by
          simp only [dw]; rw [x₄ _ (by decide) (by decide), x₃ _ (by decide) (by decide)],
        h₂.r2 i hi]
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k = 12 + i := ⟨k - 12, by omega, by omega⟩
      have a := a₆ i hi
      simp only [Nat.reduceMul] at a
      rw [show 4 * (12 + i) = 48 + 4 * i by omega, a,
        show dw s₅ .xmm3 i = dw s₂ .xmm3 i by
          simp only [dw]; rw [x₂ _ (by decide) (by decide) (by decide) (by decide)],
        h₂.r3 i hi]

/-! ## A state satisfying the precondition, and constant time -/


/-- Memory whose two argument slots (at `0x4004`) hold `0x1000` and `0x2000`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 64⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 256⟩]

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and so are the 12 bytes above it (the
return address and the two pointer arguments), which no store changes. -/
def τ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 8) (by lit_omega) (by simpa using hp.ret_buf)
    (by simpa [argR, argAddr, addr] using hp.arg_buf)

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.blockX86.pre s₁)
    (h₂ : Proof.ChaCha20.blockX86.pre s₂) (hpub : Proof.ChaCha20.blockX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₁.esp_fits
  have f₂ : (s₂.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₂.esp_fits
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86.post s s' :=
  correct (pre_of s hs)

theorem block_ct : ConstantTime isa Proof.ChaCha20.blockX86.pre Proof.ChaCha20.blockX86.pub block :=
  VG.Taint.constantTime (A := sseTaint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide)

theorem block_verified :
    Verified X86.target Impl.ChaCha20.X86.block (Spec.ChaCha20.blockContract X86.abi) :=
  Verified.of_correct block_correct block_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have e : argAddr satState 0 = 0x4004 := by decide
    have esp : satState.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.blockX86] [a0, a1, e, esp] using satState)

end VG.Proof.ChaCha20.X86
