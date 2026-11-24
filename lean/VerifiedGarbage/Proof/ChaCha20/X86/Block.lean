module

public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Impl.ChaCha20.X86
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.ChaCha20.X86.Kernels
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.ChaCha20.Spec
meta import VerifiedGarbage.Impl.ChaCha20.X86
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Spec.ChaCha20.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.ChaCha20
meta import VerifiedGarbage.TCB.Artifact

@[expose] public section

section

/-!
# ChaCha20 block function on x86 (32-bit): the rounds
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-- The address of word `k` of `buf`, relative to its 64-bit address `B`. -/
abbrev wordAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## A double round on the rows -/

/-- The column round and the diagonal round of `innerBlock`. -/
def colRound (v : CState) : CState := qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15
def diagRound (v : CState) : CState := qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

theorem innerBlock_eq (v : CState) : innerBlock v = diagRound (colRound v) := rfl

/-- The state `v` in `xmm0`–`xmm3`, a row each. -/
def Rows (v : CState) (s : State) : Prop :=
  ∀ l (hl : l < 4), dw s .xmm0 l = v[l] ∧ dw s .xmm1 l = v[4 + l] ∧ dw s .xmm2 l = v[8 + l] ∧
    dw s .xmm3 l = v[12 + l]

/-- The state `v` with row `r` rotated by `r` doublewords: each diagonal in a
column. -/
def DRows (v : CState) (s : State) : Prop :=
  ∀ l (hl : l < 4), dw s .xmm0 l = v[l] ∧ dw s .xmm1 l = v[4 + (l + 1) % 4]'(by omega_using [hl]) ∧
    dw s .xmm2 l = v[8 + (l + 2) % 4]'(by omega_using [hl]) ∧
    dw s .xmm3 l = v[12 + (l + 3) % 4]'(by omega_using [hl])

private theorem fv3 : ((3 : Fin 16) : Nat) = 3 := rfl
private theorem fv4 : ((4 : Fin 16) : Nat) = 4 := rfl
private theorem fv5 : ((5 : Fin 16) : Nat) = 5 := rfl
private theorem fv6 : ((6 : Fin 16) : Nat) = 6 := rfl
private theorem fv7 : ((7 : Fin 16) : Nat) = 7 := rfl
private theorem fv8 : ((8 : Fin 16) : Nat) = 8 := rfl
private theorem fv9 : ((9 : Fin 16) : Nat) = 9 := rfl
private theorem fv10 : ((10 : Fin 16) : Nat) = 10 := rfl
private theorem fv11 : ((11 : Fin 16) : Nat) = 11 := rfl
private theorem fv12 : ((12 : Fin 16) : Nat) = 12 := rfl
private theorem fv13 : ((13 : Fin 16) : Nat) = 13 := rfl
private theorem fv14 : ((14 : Fin 16) : Nat) = 14 := rfl
private theorem fv15 : ((15 : Fin 16) : Nat) = 15 := rfl

theorem colRound_get (v : CState) {l : Nat} (hl : l < 4) :
    (colRound v)[l] = (quarterRound v[l] v[4 + l] v[8 + l] v[12 + l]).1 ∧
    (colRound v)[4 + l] = (quarterRound v[l] v[4 + l] v[8 + l] v[12 + l]).2.1 ∧
    (colRound v)[8 + l] = (quarterRound v[l] v[4 + l] v[8 + l] v[12 + l]).2.2.1 ∧
    (colRound v)[12 + l] = (quarterRound v[l] v[4 + l] v[8 + l] v[12 + l]).2.2.2 := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> simp [colRound, qround_get, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15]

theorem diagRound_get (v : CState) {l : Nat} (hl : l < 4) :
    (diagRound v)[l] = (quarterRound v[l] (v[4 + (l + 1) % 4]'(by omega_using [hl]))
      (v[8 + (l + 2) % 4]'(by omega_using [hl])) (v[12 + (l + 3) % 4]'(by omega_using [hl]))).1 ∧
    (diagRound v)[4 + (l + 1) % 4]'(by omega_using [hl]) = (quarterRound v[l]
      (v[4 + (l + 1) % 4]'(by omega_using [hl])) (v[8 + (l + 2) % 4]'(by omega_using [hl]))
      (v[12 + (l + 3) % 4]'(by omega_using [hl]))).2.1 ∧
    (diagRound v)[8 + (l + 2) % 4]'(by omega_using [hl]) = (quarterRound v[l]
      (v[4 + (l + 1) % 4]'(by omega_using [hl])) (v[8 + (l + 2) % 4]'(by omega_using [hl]))
      (v[12 + (l + 3) % 4]'(by omega_using [hl]))).2.2.1 ∧
    (diagRound v)[12 + (l + 3) % 4]'(by omega_using [hl]) = (quarterRound v[l]
      (v[4 + (l + 1) % 4]'(by omega_using [hl])) (v[8 + (l + 2) % 4]'(by omega_using [hl]))
      (v[12 + (l + 3) % 4]'(by omega_using [hl]))).2.2.2 := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> simp [diagRound, qround_get, fv3, fv4, fv5, fv6, fv7, fv8, fv9, fv10, fv11, fv12, fv13, fv14, fv15]

/-- What a double round keeps: everything but `xmm0`–`xmm4`. -/
structure Kept (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Kept.trans {a b c : State} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- `shuf i j k`: rows 1, 2 and 3 shuffled. -/
theorem shuf_ok (i j k : BitVec 8) (s : State) :
    WP isa (.block (shuf i j k)) s fun s' => s'.xmm .xmm0 = s.xmm .xmm0 ∧
      s'.xmm .xmm1 = shufDwords (s.xmm .xmm1) i ∧ s'.xmm .xmm2 = shufDwords (s.xmm .xmm2) j ∧
      s'.xmm .xmm3 = shufDwords (s.xmm .xmm3) k ∧ Kept s s' := by
  apply WP.of_runBlock
  simp only [shuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩ <;>
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm2),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm3),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm1 = .xmm2),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm1 = .xmm3),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm2 = .xmm3),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm2 = .xmm1),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm3 = .xmm1),
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm3 = .xmm2)]

/-- The quarter round on the columns of the rows. -/
theorem col_ok {v : CState} {s : State} (h : Rows v s) :
    WP isa (.block (vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4)) s fun s' => Rows (colRound v) s' ∧ Kept s s' :=
  WP.mono (vqr_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s) fun s' ⟨q, _, g, m, rd, wr⟩ => ⟨fun l hl => by
      obtain ⟨a, b, c, d⟩ := q l hl
      obtain ⟨ha, hb, hc, hd⟩ := h l hl
      obtain ⟨ca, cb, cc, cd⟩ := colRound_get v hl
      rw [a, b, c, d, ha, hb, hc, hd]
      exact ⟨ca.symm, cb.symm, cc.symm, cd.symm⟩, ⟨g, m, rd, wr⟩⟩

/-- The quarter round on the diagonals, in columns. -/
theorem diag_ok {v : CState} {s : State} (h : DRows v s) :
    WP isa (.block (vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4)) s fun s' => DRows (diagRound v) s' ∧ Kept s s' :=
  WP.mono (vqr_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s) fun s' ⟨q, _, g, m, rd, wr⟩ => ⟨fun l hl => by
      obtain ⟨a, b, c, d⟩ := q l hl
      obtain ⟨ha, hb, hc, hd⟩ := h l hl
      obtain ⟨ca, cb, cc, cd⟩ := diagRound_get v hl
      rw [a, b, c, d, ha, hb, hc, hd]
      exact ⟨ca.symm, cb.symm, cc.symm, cd.symm⟩, ⟨g, m, rd, wr⟩⟩

/-- The rows rotated: the diagonals in columns. -/
theorem toDiag {v : CState} {s s' : State} (h : Rows v s) (h0 : s'.xmm .xmm0 = s.xmm .xmm0)
    (h1 : s'.xmm .xmm1 = shufDwords (s.xmm .xmm1) 0x39) (h2 : s'.xmm .xmm2 = shufDwords (s.xmm .xmm2) 0x4e)
    (h3 : s'.xmm .xmm3 = shufDwords (s.xmm .xmm3) 0x93) : DRows v s' := by
  intro l hl
  simp only [dw, h0, h1, h2, h3, dword_shufDwords _ _ hl]
  rcases cases4 hl with rfl | rfl | rfl | rfl
  · exact ⟨(h 0 (by decide)).1, (h 1 (by decide)).2.1, (h 2 (by decide)).2.2.1, (h 3 (by decide)).2.2.2⟩
  · exact ⟨(h 1 (by decide)).1, (h 2 (by decide)).2.1, (h 3 (by decide)).2.2.1, (h 0 (by decide)).2.2.2⟩
  · exact ⟨(h 2 (by decide)).1, (h 3 (by decide)).2.1, (h 0 (by decide)).2.2.1, (h 1 (by decide)).2.2.2⟩
  · exact ⟨(h 3 (by decide)).1, (h 0 (by decide)).2.1, (h 1 (by decide)).2.2.1, (h 2 (by decide)).2.2.2⟩

/-- The rows rotated back. -/
theorem ofDiag {v : CState} {s s' : State} (h : DRows v s) (h0 : s'.xmm .xmm0 = s.xmm .xmm0)
    (h1 : s'.xmm .xmm1 = shufDwords (s.xmm .xmm1) 0x93) (h2 : s'.xmm .xmm2 = shufDwords (s.xmm .xmm2) 0x4e)
    (h3 : s'.xmm .xmm3 = shufDwords (s.xmm .xmm3) 0x39) : Rows v s' := by
  intro l hl
  simp only [dw, h0, h1, h2, h3, dword_shufDwords _ _ hl]
  rcases cases4 hl with rfl | rfl | rfl | rfl
  · exact ⟨(h 0 (by decide)).1, (h 3 (by decide)).2.1, (h 2 (by decide)).2.2.1, (h 1 (by decide)).2.2.2⟩
  · exact ⟨(h 1 (by decide)).1, (h 0 (by decide)).2.1, (h 3 (by decide)).2.2.1, (h 2 (by decide)).2.2.2⟩
  · exact ⟨(h 2 (by decide)).1, (h 1 (by decide)).2.1, (h 0 (by decide)).2.2.1, (h 3 (by decide)).2.2.2⟩
  · exact ⟨(h 3 (by decide)).1, (h 2 (by decide)).2.1, (h 1 (by decide)).2.2.1, (h 0 (by decide)).2.2.2⟩

theorem doubleRound_ok {v : CState} {s : State} (h : Rows v s) :
    WP isa doubleRound s fun s' => Rows (innerBlock v) s' ∧ Kept s s' := by
  rw [show doubleRound = .block (vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 ++ (shuf 0x39 0x4e 0x93 ++
    (vqr .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 ++ shuf 0x93 0x4e 0x39))) by
    simp only [doubleRound, List.append_assoc]]
  refine WP.block_append (WP.mono (col_ok h) fun s₁ ⟨r₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (shuf_ok _ _ _ s₁) fun s₂ ⟨a0, a1, a2, a3, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (diag_ok (toDiag r₁ a0 a1 a2 a3)) fun s₃ ⟨r₃, k₃⟩ => ?_)
  refine WP.mono (shuf_ok _ _ _ s₃) fun s₄ ⟨b0, b1, b2, b3, k₄⟩ => ?_
  rw [innerBlock_eq]
  exact ⟨ofDiag r₃ b0 b1 b2 b3, ((k₁.trans k₂).trans k₃).trans k₄⟩

theorem rounds_ok {v : CState} {s₀ : State} (h : Rows v s₀) :
    ∀ n, WP isa (rounds n) s₀ fun s => Rows (Nat.repeat innerBlock n v) s ∧ Kept s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ ⟨hr, hk⟩ =>
      WP.mono (doubleRound_ok hr) fun _ ⟨hr', hk'⟩ => ⟨hr', hk.trans hk'⟩)

end VG.Proof.ChaCha20.X86

end

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
  addr_eq (by have := hp.buf_fits; omega_using [hd, this])

theorem eaS {d : Nat} (hd : d < 64) : addr (st s₀) d = SA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega_using [hd, this])

theorem eaA {d : Nat} (hd : d < 12) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega_using [hd, this])

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

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

/-! ## Loading the rows -/

theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-- Row `r` of the state at `p`: its words `4 r`, …, `4 r + 3`. -/
theorem row_read (m : Mem) (p : Addr) {r l : Nat} (hl : l < 4) :
    dword (m.readW (p + BitVec.ofNat 64 (16 * r)) 128) l = m.readW (p + BitVec.ofNat 64 (4 * (4 * r + l))) 32 := by
  rw [dword_readW _ _ hl, Offset.add_add, show 16 * r + 4 * l = 4 * (4 * r + l) by omega_arith]

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_row {r : Nat} (hr : r < 4) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (16 * r)) 16 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by lit_omega) (by lit_omega)⟩

/-- A row of the input state, after writes to `buf` only. -/
theorem read_row {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {r l : Nat} (hr : r < 4) (hl : l < 4) :
    dword (m.readW (SA s₀ + BitVec.ofNat 64 (16 * r)) 128) l = (V s₀)[4 * r + l]'(by omega_using [hr, hl]) := by
  rw [row_read _ _ hl]
  exact hp.read_st hf (by omega_using [hr, hl])

end Pre

theorem row_ne4 {r : Nat} : ¬row r = XReg.xmm4 := by
  unfold row; split <;> decide

theorem row_ne5 {r : Nat} : ¬row r = XReg.xmm5 := by
  unfold row; split <;> decide

theorem row_inj {r r' : Nat} (hr : r < 4) (hr' : r' < 4) (h : r ≠ r') : ¬row r' = row r := by
  rcases cases4 hr with rfl | rfl | rfl | rfl <;> rcases cases4 hr' with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h | decide

theorem dword_movd (w : Word) : dword ((0 : BitVec 96) ++ w) 0 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add, hi,
    decide_true, Bool.true_and, ↓reduceIte]

/-- The load invariant after `n` rows. -/
structure LI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  rows : ∀ r l (hr : r < 4) (hl : l < 4), r < n →
    dword (s.xmm (row r)) l = (V s₀)[4 * r + l]'(by omega_using [hr, hl])
  keep : ∀ q, q ≠ .edx → s.gpr q = s₁.gpr q
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rowIn_ok {s₀ s₁ : State} (hp : Pre s₀) (heax : s₁.gpr .eax = st s₀) {n : Nat} (hn : n < 4)
    {s : State} (h : LI s₀ s₁ n s) : WP isa (.block (rowIn n)) s (LI s₀ s₁ (n + 1)) := by
  obtain ha : s.gpr .eax = st s₀ := (h.keep _ (by decide)).trans heax
  obtain ea : ∀ k, k < 4 → (st s₀ + BitVec.ofNat 32 (16 * n + 4 * k)).setWidth 64 =
      SA s₀ + BitVec.ofNat 64 (4 * (4 * n + k)) := fun k hk => by
    rw [show 4 * (4 * n + k) = 16 * n + 4 * k by omega_arith]
    exact hp.eaS (by omega_using [hn, hk])
  obtain hin : ∀ k, k < 4 → InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * (4 * n + k))) 4 := fun k hk => by
    rw [h.rd]; exact hp.in_st (by omega_using [hn, hk]) _
  obtain hv : ∀ k (hk : k < 4), s.mem.readW (SA s₀ + BitVec.ofNat 64 (4 * (4 * n + k))) 32 =
      (V s₀)[4 * n + k]'(by omega_using [hn, hk]) := fun k hk => by
    rw [h.mem]; exact hp.read_st (Frame.refl _ _) (by omega_using [hn, hk])
  obtain e0 := ea 0 (by decide); obtain e1 := ea 1 (by decide)
  obtain e2 := ea 2 (by decide); obtain e3 := ea 3 (by decide)
  obtain i0 := hin 0 (by decide); obtain i1 := hin 1 (by decide)
  obtain i2 := hin 2 (by decide); obtain i3 := hin 3 (by decide)
  obtain v0 := hv 0 (by decide); obtain v1 := hv 1 (by decide)
  obtain v2 := hv 2 (by decide); obtain v3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, rowIn, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    readSrc, State.load32, State.ea, at_, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ha, e0, e1, e2,
    e3, i0, i1, i2, i3, v0, v1, v2, v3, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r l hr hl hrn => ?_, fun q hq => ?_, h.mem, h.rd, h.wr⟩
  · by_cases hrn' : r = n
    · subst hrn'
      simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ row_ne4, RegUpd.xmm_setXmm_of_ne _ _ row_ne5,
        RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm4 = .xmm5), RegUpd.xmm_setReg, punpckldq_eq,
        punpcklqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_movd]
      rcases cases4 hl with rfl | rfl | rfl | rfl
      · exact dword_ofDwords_0 ..
      · exact dword_ofDwords_1 ..
      · exact dword_ofDwords_2 ..
      · exact dword_ofDwords_3 ..
    · simp only [RegUpd.xmm_setXmm_of_ne _ _ (row_inj hn hr (Ne.symm hrn')), RegUpd.xmm_setXmm_of_ne _ _ row_ne4,
        RegUpd.xmm_setXmm_of_ne _ _ row_ne5, RegUpd.xmm_setReg]
      exact h.rows r l hr hl (by omega_using [hrn, hrn'])
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne _ _ hq]
    exact h.keep q hq

/-- The pointers in `eax` and `ecx`, and the input state in the rows. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block rowsIn) s₀ fun s₁ => Rows (V s₀) s₁ ∧ s₁.gpr .eax = st s₀ ∧ s₁.gpr .ecx = bp s₀ ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s₀.gpr r) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr := by
  refine WP.block_append ?_
  refine Wp.wp_ldm rfl (hp.in_arg (i := 0) (by lit_omega)) fun s₁ u₁ => ?_
  refine Wp.wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.in_arg (i := 1) (by lit_omega))
    fun s₂ u₂ => WP.block_nil ?_
  obtain hA : s₂.gpr .eax = st s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  obtain hC : s₂.gpr .ecx = bp s₀ := by rw [u₂.gpr, u₁.mem]; rfl
  obtain h₀ : LI s₀ s₂ 0 s₂ := ⟨fun _ _ _ _ h => absurd h (by omega_arith), fun _ _ => rfl, by rw [u₂.mem, u₁.mem],
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (LI s₀ s₂) (fun k s hk h => rowIn_ok hp hA hk h) 4
    (Nat.le_refl _) s₂ h₀) fun s₃ h₃ => ?_
  refine ⟨fun l hl => ?_, by rw [h₃.keep _ (by decide), hA], by rw [h₃.keep _ (by decide), hC],
    fun r h1 h2 h3 => by rw [h₃.keep _ h3, u₂.other _ h2, u₁.other _ h1], h₃.mem, h₃.rd, h₃.wr⟩
  exact ⟨by simpa [Impl.ChaCha20.X86.row] using h₃.rows 0 l (by decide) hl (by decide),
    by simpa [Impl.ChaCha20.X86.row] using h₃.rows 1 l (by decide) hl (by decide),
    by simpa [Impl.ChaCha20.X86.row] using h₃.rows 2 l (by decide) hl (by decide),
    by simpa [Impl.ChaCha20.X86.row] using h₃.rows 3 l (by decide) hl (by decide)⟩

/-! ## Adding the input state -/

/-- The register of a row, read by cases. -/
theorem Rows.row {v : CState} {s : State} (h : Rows v s) {r l : Nat} (hr : r < 4) (hl : l < 4) :
    dw s (row r) l = v[4 * r + l]'(by omega_using [hr, hl]) := by
  rcases cases4 hr with rfl | rfl | rfl | rfl
  · simpa [Impl.ChaCha20.X86.row] using (h l hl).1
  · simpa [Impl.ChaCha20.X86.row] using (h l hl).2.1
  · simpa [Impl.ChaCha20.X86.row] using (h l hl).2.2.1
  · simpa [Impl.ChaCha20.X86.row] using (h l hl).2.2.2

/-- The add invariant after `n` rows, relative to the state `sB` after the rounds. -/
structure AI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), j < 4 * n → s.mem.readW (wordAddr (BA s₀) j) 32 = (Rs s₀)[j] + (V s₀)[j]
  rows : ∀ r, r < 4 → n ≤ r → s.xmm (row r) = sB.xmm (row r)
  gpr : s.gpr = sB.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [bufR s₀] s₀.mem s.mem

theorem add_step {s₀ sB : State} (hp : Pre s₀) (hR : Rows (Rs s₀) sB) (heax : sB.gpr .eax = st s₀)
    (hecx : sB.gpr .ecx = bp s₀) {n : Nat} (hn : n < 4) {s : State} (ha : AI s₀ sB n s) :
    WP isa (.block (addRow n)) s (AI s₀ sB (n + 1)) := by
  obtain eS : s.ea (at_ .eax (16 * n)) = SA s₀ + BitVec.ofNat 64 (16 * n) := by
    show addr (s.gpr .eax) (16 * n) = _
    rw [ha.gpr, heax]; exact hp.eaS (by omega_using [hn])
  obtain eB : s.ea (at_ .ecx (16 * n)) = BA s₀ + BitVec.ofNat 64 (16 * n) := by
    show addr (s.gpr .ecx) (16 * n) = _
    rw [ha.gpr, hecx]; exact hp.eaB (by omega_using [hn])
  obtain iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (16 * n)) 16 := by
    rw [ha.rd]; exact hp.in_row hn _
  obtain oB : InRegions s.wr (BA s₀ + BitVec.ofNat 64 (16 * n)) 16 := by
    rw [ha.wr]; exact hp.out_buf (by omega_using [hn])
  apply WP.of_runBlock
  simp only [addRow, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, ea_setXmm', RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, RegUpd.gpr_setXmm, eS,
    eB, iS, oB, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj hjn => ?_, fun r hr hnr => ?_, ha.gpr, ha.rd, ha.wr,
    ha.fb.writeW (List.mem_singleton_self _) _ (contains_off (by omega_using [hn]) (by lit_omega))⟩
  · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ row_ne4]
    by_cases hlt : j < 4 * n
    · rw [show wordAddr (BA s₀) j = BA s₀ + BitVec.ofNat 64 (4 * j) from rfl,
        Mem.readW_writeW_sep (Offset.sep (BA s₀) (.inl (by omega_using [hlt])) (by omega_using [hj])
          (by omega_using [hn])) (by decide)]
      exact ha.out j hj hlt
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < 4 ∧ j = 4 * n + l := ⟨j - 4 * n, by omega_using [hlt, hjn], by omega_using [hlt]⟩
      rw [show wordAddr (BA s₀) (4 * n + l) = BA s₀ + BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 (4 * l) by
        rw [Offset.add_add, show 16 * n + 4 * l = 4 * (4 * n + l) by omega_arith], readW_writeW128 _ _ _ hl,
        dword_paddd _ _ hl, ha.rows n hn (Nat.le_refl _), hp.read_row ha.fb hn hl]
      exact congrArg (· + _) (hR.row hn hl)
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ (row_inj hn hr (by omega_using [hnr])),
      RegUpd.xmm_setXmm_of_ne _ _ row_ne4]
    exact ha.rows r hr (by omega_using [hnr])

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (wordAddr p j) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' => abiPreserved s₀ s' ∧ Proof.ChaCha20.blockX86.post s₀ s' := by
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨r₁, a₁, c₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok r₁ 10) fun s₂ ⟨r₂, k₂⟩ => ?_)
  obtain ha₀ : AI s₀ s₂ 0 s₂ := ⟨fun _ _ h => absurd h (by omega_arith), fun _ _ _ => rfl, rfl,
    k₂.rd.trans rd₁, k₂.wr.trans wr₁, by rw [k₂.mem, m₁]; exact Frame.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (AI s₀ s₂)
    (fun k s hk ha => add_step hp r₂ (by rw [k₂.gpr]; exact a₁) (by rw [k₂.gpr]; exact c₁) hk ha) 4
    (Nat.le_refl _) s₂ ha₀) fun s' hA => ?_
  obtain hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [hA.gpr, k₂.gpr]; exact g₁ r h1 h2 h3
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)
  · refine hA.fb.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simpa using hp.ret_buf
  · show stateAt s'.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
    exact block_post fun j hj => hA.out j hj (by omega_using [hj])

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
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega_using [hk]
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86.post s s' :=
  correct (pre_of s hs)

theorem block_ct : ConstantTime isa Proof.ChaCha20.blockX86.pre Proof.ChaCha20.blockX86.pub block :=
  VG.Taint.constantTime (A := sseTaint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide)

end VG.Proof.ChaCha20.X86
