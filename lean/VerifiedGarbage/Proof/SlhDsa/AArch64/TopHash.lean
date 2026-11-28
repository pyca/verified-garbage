module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake
import VerifiedGarbage.Proof.Framework.RelSteps
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `H_msg` and `PRF_msg`

`Shake.hashM' p f xs dst len` (`Impl/SlhDsa/AArch64/Shake.lean`) zeroes the
Keccak state at `oStream`, absorbs the strings `xs` of `n` bytes each, then
`M′ = 0 ‖ ctx_len ‖ ctx ‖ M` (its header at `oHdr`, `ctx` and its length in
`x22` and `x23`, `M` and its length in `x20` and `x21`), pads and squeezes
`len` bytes to `dst` (`hashM_ok`): `SHAKE256(x₁ ‖ … ‖ M′, len)`. It changes
only the Keccak state and its working space, `dst` and the 16 bytes below
the stack pointer, and registers that are not callee-saved (or `x30`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep Kept stk wp_nil wp_x wp_movz wp_addImm absorb_callWith pad_callWith
  squeeze_callWith)
open VG.Spec.Sha3 (bytesAt Repr stateAt absorb pad squeezeFrom rates)
open VG.Impl.SlhDsa.AArch64
open VG.Impl.SlhDsa.AArch64.Shake (Arg Fns)

/-- The single-state Keccak of the variant, as a proven permutation. -/
def kperm (sha3 : Bool) : Proof.Sha3.AArch64.Permutation :=
  if sha3 then Proof.Sha3.AArch64.Sha3.Vector.backend else Proof.Sha3.AArch64.Scalar.backend

theorem kperm_callee (sha3 : Bool) : (kperm sha3).callee = Shake.keccakOf sha3 := by
  cases sha3 <;> rfl

/-! ## Arguments -/

/-- The value an argument gives its register, in `s`. -/
def argVal (s : State) : Arg → BitVec 64
  | .reg r => s.gpr r
  | .scr o => s.gpr .x19 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .ret => s.gpr .x0

/-- An argument the moves of a call can set: a register none of them writes,
an offset or an immediate that fits. -/
def ArgOk : Arg → Prop
  | .reg r => r ∉ [.x0, .x1, .x2, .x3, .x4, .x5]
  | .scr o => o < 4096
  | .imm v => v < 2 ^ 64
  | .ret => True

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem argMov_ok {d : Reg} {a : Arg} (ha : ArgOk a)
    (k : ∀ s', Only [d] s s' → s'.gpr d = argVal s a → WP isa (.block is) s' Q) :
    WP isa (.block (a.mov d ++ is)) s Q := by
  cases a with
  | reg r => exact MlKem.AArch64.wp_addImm (by decide) fun s' o e => k s' o (by rw [e]; exact BitVec.add_zero _)
  | scr o => exact lea_ok (.inl ha) (Nat.lt_trans ha (by decide)) k
  | imm v => exact movV_ok ha k
  | ret => exact MlKem.AArch64.wp_addImm (by decide) fun s' o e => k s' o (by rw [e]; exact BitVec.add_zero _)

theorem argVal_of_only {rs : List Reg} {s s' : State} (h : Only rs s s') {a : Arg} (ha : ArgOk a)
    (hr : ∀ r ∈ rs, r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5]) (h19 : .x19 ∉ rs) (hret : a ≠ .ret) :
    argVal s' a = argVal s a := by
  cases a with
  | reg r => exact h.gpr r fun hm => ha (hr r hm)
  | scr o => simp only [argVal, h.gpr .x19 h19]
  | imm v => rfl
  | ret => exact absurd rfl hret

end

/-! ## The calls of the sponge functions -/

/-- The Keccak state and its working space, in `scratch` at `S`. -/
abbrev stR (S : Addr) : Region := ⟨at' S Layout.oStream, 200⟩
abbrev wkR (S : Addr) : Region := ⟨at' S (Layout.oStream + 200), 640⟩

theorem st_wk (S : Addr) : (stR S).Disjoint (wkR S) :=
  Offset.disjoint S (by simp only [Layout.oStream]; omega) (by simp only [Layout.oStream]; omega)
    (by simp only [Layout.oStream]; omega)

/-- What the sponge functions' calls need of the state `s`, with `scratch` at `S`. -/
structure KS (s : State) (S : Addr) : Prop where
  x19 : s.gpr .x19 = S
  sp16 : 16 ≤ s.sp.toNat
  kst : (stk s).Disjoint (stR S)
  kwk : (stk s).Disjoint (wkR S)
  cov : Covers [stR S, wkR S] s.wr

theorem KS.kept {s s' : State} {S : Addr} {rs : List Region} (h : KS s S) (hk : Kept rs s s') : KS s' S :=
  ⟨by rw [hk.cs .x19 (by decide) (by decide), h.x19], by rw [hk.sp]; exact h.sp16,
    by rw [show stk s' = stk s by simp only [stk, hk.sp]]; exact h.kst,
    by rw [show stk s' = stk s by simp only [stk, hk.sp]]; exact h.kwk, by rw [hk.wr]; exact h.cov⟩

theorem KS.keep {s s' : State} {S : Addr} {rs : List Reg} (h : KS s S) (hk : Keep rs s s')
    (h19 : Reg.x19 ∉ rs) : KS s' S :=
  ⟨by rw [hk.gpr .x19 h19, h.x19], by rw [hk.sp]; exact h.sp16,
    by rw [show stk s' = stk s by simp only [stk, hk.sp]]; exact h.kst,
    by rw [show stk s' = stk s by simp only [stk, hk.sp]]; exact h.kwk, by rw [hk.wr]; exact h.cov⟩

theorem toNat_136 : (BitVec.ofNat 64 136).toNat = 136 := rfl

theorem rate136 : (136 : Nat) ∈ rates := by simp [rates]

/-- A piece the sponge reads, at `s`. -/
structure PieceIn (s : State) (S : Addr) (a : Addr) (l : Nat) : Prop where
  dst : Region.Disjoint ⟨a, l⟩ (stR S)
  dwk : Region.Disjoint ⟨a, l⟩ (wkR S)
  stk : (stk s).Disjoint ⟨a, l⟩
  cov : Covers [⟨a, l⟩] (s.rd ++ s.wr)

/-- A call of `vg_keccak_absorb_scratch`: the `l` bytes at `src` absorbed
from the position `pos`. -/
theorem kabs_ok (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {src len pos : Arg}
    (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos) (hsr : src ≠ .ret) (hlr : len ≠ .ret)
    {s : State} {S : Addr} (H : KS s S) {msg : List Byte} (hr : Repr s.mem (at' S Layout.oStream) 136 msg)
    (hq : (argVal s pos).toNat = msg.length % 136)
    (hpc : PieceIn s S (argVal s src) (argVal s len).toNat) :
    WP isa (Shake.kabs f src len pos) s fun s' => Kept [stR S, wkR S, below s.sp 16] s s' ∧
      Repr s'.mem (at' S Layout.oStream) 136 (msg ++ bytesAt s.mem (argVal s src) (argVal s len).toNat) ∧
      (s'.gpr .x0).toNat = (msg.length + (argVal s len).toNat) % 136 := by
  unfold Shake.kabs Shake.callA
  simp only [hv]
  refine WP.seq ?_
  refine argMov_ok (d := .x2) hp fun s₁ o₁ e₁ =>
    argMov_ok (d := .x0) (a := .scr Layout.oStream) (show Layout.oStream < 4096 by decide) fun s₂ o₂ e₂ =>
    argMov_ok (d := .x1) (a := .imm 136) (show 136 < 2 ^ 64 by decide) fun s₃ o₃ e₃ =>
    argMov_ok (d := .x3) hs fun s₄ o₄ e₄ => argMov_ok (d := .x4) hl fun s₅ o₅ e₅ =>
    argMov_ok (d := .x5) (a := .scr (Layout.oStream + 200)) (show Layout.oStream + 200 < 4096 by decide)
      fun s₆ o₆ e₆ => wp_nil ?_
  have O := ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆
  have v₂ : argVal s₁ (.scr Layout.oStream) = at' S Layout.oStream := by
    simp only [argVal, o₁.get .x19 (by simp), H.x19]
  have v₆ : argVal s₅ (.scr (Layout.oStream + 200)) = at' S (Layout.oStream + 200) := by
    simp only [argVal, o₅.get .x19 (by simp), o₄.get .x19 (by simp), o₃.get .x19 (by simp), o₂.get .x19 (by simp),
      o₁.get .x19 (by simp), H.x19]
  have v₄ : argVal s₃ src = argVal s src :=
    argVal_of_only ((o₁.trans o₂).trans o₃) hs (by decide) (by decide) hsr
  have v₅ : argVal s₄ len = argVal s len :=
    argVal_of_only (((o₁.trans o₂).trans o₃).trans o₄) hl (by decide) (by decide) hlr
  have k₆ := O.keep
  refine absorb_callWith v (st := at' S Layout.oStream) (dt := argVal s src) (sc := at' S (Layout.oStream + 200))
    (rate := 136) (pos := msg.length % 136) (len := (argVal s len).toNat)
    (by rw [o₆.get .x0, o₅.get .x0, o₄.get .x0, o₃.get .x0, e₂, v₂])
    (by rw [o₆.get .x1, o₅.get .x1, o₄.get .x1, e₃]; rfl)
    (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, o₂.get .x2, e₁, hq])
    (by rw [o₆.get .x3, o₅.get .x3, e₄, v₄])
    (by rw [o₆.get .x4, e₅, v₅])
    (by rw [e₆, v₆]) rate136 (Nat.mod_lt _ (by decide)) (st_wk S) hpc.dst hpc.dwk
    (by rw [k₆.sp]; exact H.sp16) (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact H.kst)
    (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact hpc.stk)
    (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact H.kwk)
    (by rw [k₆.rd, k₆.wr]; exact Covers.cons (MlKem.AArch64.Covers.head hpc.cov) (Covers.right H.cov))
    (by rw [k₆.wr]; exact H.cov) fun s' kp rp xp => ?_
  have m₆ : s₆.mem = s.mem := by rw [O.mem]
  have kk : Kept [stR S, wkR S, below s.sp 16] s s' := by
    have k0 : Kept [] s s₆ := MlKem.AArch64.Kept.of_keep k₆ m₆ (by decide)
    rw [show below s₆.sp 16 = below s.sp 16 by rw [k₆.sp]] at kp
    exact (k0.mono (by simp)).trans kp
  refine ⟨kk, ?_, ?_⟩
  · have := rp msg (by rw [m₆]; exact hr) rfl
    rwa [m₆] at this
  · rw [xp]; omega_using []

/-- A call of `vg_keccak_pad_scratch`, with SHAKE's suffix, from the position `pos`. -/
theorem kpad_ok (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {pos : Arg}
    (hp : ArgOk pos) {s : State} {S : Addr} (H : KS s S) {msg : List Byte}
    (hr : Repr s.mem (at' S Layout.oStream) 136 msg) (hq : (argVal s pos).toNat = msg.length % 136) :
    WP isa (Shake.kpad f pos) s fun s' => Kept [stR S, wkR S, below s.sp 16] s s' ∧
      stateAt s'.mem (at' S Layout.oStream) = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold Shake.kpad Shake.callA
  simp only [hv]
  refine WP.seq ?_
  refine argMov_ok (d := .x2) hp fun s₁ o₁ e₁ =>
    argMov_ok (d := .x0) (a := .scr Layout.oStream) (show Layout.oStream < 4096 by decide) fun s₂ o₂ e₂ =>
    argMov_ok (d := .x1) (a := .imm 136) (show 136 < 2 ^ 64 by decide) fun s₃ o₃ e₃ =>
    argMov_ok (d := .x3) (a := .imm 0x1f) (show 0x1f < 2 ^ 64 by decide) fun s₄ o₄ e₄ =>
    argMov_ok (d := .x4) (a := .scr (Layout.oStream + 200)) (show Layout.oStream + 200 < 4096 by decide)
      fun s₅ o₅ e₅ => wp_nil ?_
  have O := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  have v₂ : argVal s₁ (.scr Layout.oStream) = at' S Layout.oStream := by
    simp only [argVal, o₁.get .x19 (by simp), H.x19]
  have v₅ : argVal s₄ (.scr (Layout.oStream + 200)) = at' S (Layout.oStream + 200) := by
    simp only [argVal, o₄.get .x19 (by simp), o₃.get .x19 (by simp), o₂.get .x19 (by simp),
      o₁.get .x19 (by simp), H.x19]
  have k₅ := O.keep
  refine pad_callWith v (st := at' S Layout.oStream) (sc := at' S (Layout.oStream + 200))
    (rate := 136) (pos := msg.length % 136)
    (by rw [o₅.get .x0, o₄.get .x0, o₃.get .x0, e₂, v₂])
    (by rw [o₅.get .x1, o₄.get .x1, e₃]; rfl)
    (by rw [o₅.get .x2, o₄.get .x2, o₃.get .x2, o₂.get .x2, e₁, hq])
    (by rw [e₅, v₅]) rate136 (Nat.mod_lt _ (by decide)) (st_wk S)
    (by rw [k₅.sp]; exact H.sp16) (by rw [show stk s₅ = stk s by simp only [stk, k₅.sp]]; exact H.kst)
    (by rw [show stk s₅ = stk s by simp only [stk, k₅.sp]]; exact H.kwk)
    (by rw [k₅.rd, k₅.wr]; exact Covers.right H.cov)
    (by rw [k₅.wr]; exact H.cov) fun s' kp rp => ?_
  have m₅ : s₅.mem = s.mem := by rw [O.mem]
  have kk : Kept [stR S, wkR S, below s.sp 16] s s' := by
    have k0 : Kept [] s s₅ := MlKem.AArch64.Kept.of_keep k₅ m₅ (by decide)
    rw [show below s₅.sp 16 = below s.sp 16 by rw [k₅.sp]] at kp
    exact (k0.mono (by simp)).trans kp
  refine ⟨kk, ?_⟩
  have := rp msg (by rw [m₅]; exact hr) rfl
  rw [this, o₅.get .x3, e₄]
  rfl

/-- A piece the sponge writes, at `s`. -/
structure PieceOut (s : State) (S : Addr) (a : Addr) (l : Nat) : Prop where
  dst : Region.Disjoint (stR S) ⟨a, l⟩
  dwk : Region.Disjoint ⟨a, l⟩ (wkR S)
  stk : (stk s).Disjoint ⟨a, l⟩
  cov : Covers [⟨a, l⟩] s.wr

/-- A call of `vg_keccak_squeeze_scratch`: `len` bytes from position 0 to `dst`. -/
theorem ksqz_ok (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {dst : Arg} {len : Nat}
    (hd : ArgOk dst) (hdr : dst ≠ .ret) (hl : len < 2 ^ 64) {s : State} {S : Addr} (H : KS s S)
    (hpc : PieceOut s S (argVal s dst) len) :
    WP isa (Shake.ksqz f dst len) s fun s' =>
      Kept [stR S, ⟨argVal s dst, len⟩, wkR S, below s.sp 16] s s' ∧
      bytesAt s'.mem (argVal s dst) len = squeezeFrom 136 (stateAt s.mem (at' S Layout.oStream)) 0 len := by
  unfold Shake.ksqz Shake.callA
  simp only [hv]
  refine WP.seq ?_
  refine argMov_ok (d := .x2) (a := .imm 0) (show 0 < 2 ^ 64 by decide) fun s₁ o₁ e₁ =>
    argMov_ok (d := .x0) (a := .scr Layout.oStream) (show Layout.oStream < 4096 by decide) fun s₂ o₂ e₂ =>
    argMov_ok (d := .x1) (a := .imm 136) (show 136 < 2 ^ 64 by decide) fun s₃ o₃ e₃ =>
    argMov_ok (d := .x3) hd fun s₄ o₄ e₄ => argMov_ok (d := .x4) (a := .imm len) hl fun s₅ o₅ e₅ =>
    argMov_ok (d := .x5) (a := .scr (Layout.oStream + 200)) (show Layout.oStream + 200 < 4096 by decide)
      fun s₆ o₆ e₆ => wp_nil ?_
  have O := ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆
  have v₂ : argVal s₁ (.scr Layout.oStream) = at' S Layout.oStream := by
    simp only [argVal, o₁.get .x19 (by simp), H.x19]
  have v₆ : argVal s₅ (.scr (Layout.oStream + 200)) = at' S (Layout.oStream + 200) := by
    simp only [argVal, o₅.get .x19 (by simp), o₄.get .x19 (by simp), o₃.get .x19 (by simp), o₂.get .x19 (by simp),
      o₁.get .x19 (by simp), H.x19]
  have v₄ : argVal s₃ dst = argVal s dst :=
    argVal_of_only ((o₁.trans o₂).trans o₃) hd (by decide) (by decide) hdr
  have k₆ := O.keep
  have hcov : Covers [stR S, ⟨argVal s dst, len⟩, wkR S] s.wr :=
    Covers.cons (MlKem.AArch64.Covers.head H.cov) (Covers.cons hpc.cov (MlKem.AArch64.Covers.tail H.cov))
  refine squeeze_callWith v (st := at' S Layout.oStream) (out := argVal s dst) (sc := at' S (Layout.oStream + 200))
    (rate := 136) (pos := 0) (len := len)
    (by rw [o₆.get .x0, o₅.get .x0, o₄.get .x0, o₃.get .x0, e₂, v₂])
    (by rw [o₆.get .x1, o₅.get .x1, o₄.get .x1, e₃]; rfl)
    (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, o₂.get .x2, e₁]; rfl)
    (by rw [o₆.get .x3, o₅.get .x3, e₄, v₄])
    (by rw [o₆.get .x4, e₅]; simp only [argVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl])
    (by rw [e₆, v₆]) rate136 (by decide) hpc.dst (st_wk S) hpc.dwk
    (by rw [k₆.sp]; exact H.sp16) (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact H.kst)
    (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact hpc.stk)
    (by rw [show stk s₆ = stk s by simp only [stk, k₆.sp]]; exact H.kwk)
    (by rw [k₆.rd, k₆.wr]; exact Covers.right hcov) (by rw [k₆.wr]; exact hcov) fun s' kp bp _ _ => ?_
  have m₆ : s₆.mem = s.mem := by rw [O.mem]
  have kk : Kept [stR S, ⟨argVal s dst, len⟩, wkR S, below s.sp 16] s s' := by
    have k0 : Kept [] s s₆ := MlKem.AArch64.Kept.of_keep k₆ m₆ (by decide)
    rw [show below s₆.sp 16 = below s.sp 16 by rw [k₆.sp]] at kp
    exact (k0.mono (by simp)).trans kp
  refine ⟨kk, ?_⟩
  rw [bp, m₆]

/-! ## `hashM'` -/

/-- An argument naming a piece of memory: a callee-saved register (not
`x30`), which the calls keep, or an offset of `scratch`. -/
def PieceArg : Arg → Prop
  | .reg r => r ∈ preserved ∧ r ≠ .x30 ∧ r ∉ [.x0, .x1, .x2, .x3, .x4, .x5]
  | .scr o => o < 4096
  | _ => False

theorem PieceArg.ok {a : Arg} (h : PieceArg a) : ArgOk a := by
  cases a with
  | reg r => exact h.2.2
  | scr o => exact h
  | imm _ => exact absurd h id
  | ret => exact absurd h id

theorem PieceArg.ne {a : Arg} (h : PieceArg a) : a ≠ .ret := by
  cases a <;> first | exact absurd h id | simp

theorem argVal_kept {rs : List Region} {s s' : State} (hk : Kept rs s s') {a : Arg} (h : PieceArg a) :
    argVal s' a = argVal s a := by
  cases a with
  | reg r => exact hk.cs r h.1 h.2.1
  | scr o => simp only [argVal, hk.cs .x19 (by decide) (by decide)]
  | imm _ => exact absurd h id
  | ret => exact absurd h id

/-- What the hash needs, at its entry state `s`. -/
structure HashIn (n : Nat) (s : State) (S : Addr) (xs : List Arg) (dst : Arg) (len : Nat) : Prop where
  ks : KS s S
  pieces : ∀ x ∈ xs, PieceArg x ∧ PieceIn s S (argVal s x) n
  piecesLen : n * xs.length < 136
  hdr : PieceIn s S (at' S Layout.oHdr) 2
  ctx : PieceIn s S (s.gpr .x22) (s.gpr .x23).toNat
  msg : PieceIn s S (s.gpr .x20) (s.gpr .x21).toNat
  dstA : PieceArg dst
  dst : PieceOut s S (argVal s dst) len
  len : len < 2 ^ 64

/-- The regions the hash changes. -/
abbrev hashR (s : State) (S : Addr) : List Region := [stR S, wkR S, below s.sp 16]

theorem PieceIn.kept {s s' : State} {S a : Addr} {l : Nat} {rs : List Region} (h : PieceIn s S a l)
    (hk : Kept rs s s') : PieceIn s' S a l :=
  ⟨h.dst, h.dwk, (show MlKem.AArch64.stk s' = MlKem.AArch64.stk s by simp only [MlKem.AArch64.stk, hk.sp]) ▸ h.stk,
    by rw [hk.rd, hk.wr]; exact h.cov⟩

/-- A piece's bytes, past changes to the hash's regions. -/
theorem PieceIn.bytes {s s' : State} {S a : Addr} {l : Nat} (h : PieceIn s S a l)
    (hf : Frame (hashR s S) s.mem s'.mem) (hl : l ≤ 2 ^ 64) : bytesAt s'.mem a l = bytesAt s.mem a l :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.dst
    · exact h.dwk
    · exact h.stk.symm) hl

theorem kept_trans {s t u : State} {S : Addr} (h₁ : Kept (hashR s S) s t) (h₂ : Kept (hashR t S) t u) :
    Kept (hashR s S) s u := by
  have e : hashR t S = hashR s S := by simp only [hashR, h₁.sp]
  rw [e] at h₂; exact h₁.trans h₂

theorem bytesAt_length (m : Mem) (a : Addr) (l : Nat) : (bytesAt m a l).length = l := by simp [bytesAt]

/-- The absorbs of the strings `ys`, the first at position `n j`. -/
private theorem pieces_ok (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {n : Nat}
    (hn : n ≤ 32) {s : State} {S : Addr} {rest : Prog isa} {Q : State → Prop} :
    ∀ (ys : List Arg) (j : Nat) (st : State) (msg : List Byte), n * (j + ys.length) < 136 →
      (∀ y ∈ ys, PieceArg y ∧ PieceIn s S (argVal s y) n) → KS s S → Kept (hashR s S) s st →
      Repr st.mem (at' S Layout.oStream) 136 msg → msg.length = n * j →
      (∀ st', Kept (hashR s S) s st' →
        Repr st'.mem (at' S Layout.oStream) 136 (msg ++ (ys.map fun y => bytesAt s.mem (argVal s y) n).flatten) →
        WP isa rest st' Q) →
      WP isa ((ys.zipIdx j).foldr (fun (x, i) c => .seq (Shake.kabs f x (.imm n) (.imm (n * i))) c) rest) st Q
  | [], j, st, msg, _, _, _, hk, hr, _, k => by
    simpa using k st hk (by simpa using hr)
  | y :: ys, j, st, msg, hb, hy, H, hk, hr, hl, k => by
    rw [List.zipIdx_cons, List.foldr_cons]
    obtain ⟨ya, yp⟩ := hy y List.mem_cons_self
    have Hs := H.kept hk
    have hj : n * j < 136 := by
      have := Nat.mul_le_mul_left n (show j ≤ j + (y :: ys).length by omega_using [])
      omega_using [hb, this]
    refine WP.seq (WP.mono (kabs_ok v hv (src := y) (len := .imm n) (pos := .imm (n * j)) ya.ok
      (show n < 2 ^ 64 by omega_using [hn]) (show n * j < 2 ^ 64 by omega_using [hj]) ya.ne (by simp) Hs hr
      (by simp only [argVal, BitVec.toNat_ofNat]; omega_using [hj, hl])
      (by rw [argVal_kept hk ya]; simpa [argVal, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [hn])] using
        yp.kept hk)) fun st' ⟨k', r', _⟩ => ?_)
    have hk' := kept_trans hk k'
    rw [show argVal st (.imm n) = BitVec.ofNat 64 n from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [hn]), argVal_kept hk ya,
      yp.bytes hk.frame (by omega_using [hn])] at r'
    refine pieces_ok v hv hn ys (j + 1) st' _ (by
        simp only [List.length_cons] at hb; rw [show j + 1 + ys.length = j + (ys.length + 1) by omega_using []]; exact hb)
      (fun z hz => hy z (List.mem_cons_of_mem _ hz)) H hk' r'
      (by rw [List.length_append, hl, bytesAt_length, Nat.mul_succ]) fun st'' k'' r'' => k st'' k'' ?_
    simpa only [List.map_cons, List.flatten_cons, List.append_assoc] using r''

theorem readW_zero {m : Mem} {a : Addr} (h : ∀ i < 8, m (a + BitVec.ofNat 64 i) = 0) : m.readW a 64 = 0 := by
  simp only [Mem.readW]
  rw [Mem.read_eq_of_bytes (v := 0) fun i hi => by rw [h i hi]; apply BitVec.eq_of_toNat_eq; simp]
  rfl

/-- `zeroState`: the Keccak state zeroed. -/
theorem zeroState_ok {s : State} {S : Addr} (H : KS s S) :
    WP isa (.block Shake.zeroState) s fun s' => Kept (hashR s S) s s' ∧
      stateAt s'.mem (at' S Layout.oStream) = Spec.Sha3.zero := by
  have hin : InRegions s.wr (at' S Layout.oStream) 200 :=
    MlKem.AArch64.Covers.head H.cov _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [Shake.zeroState, ← List.append_nil (zeroWords .x9 0 25), List.singleton_append]
  refine MlKem.AArch64.wp_addImm (by decide) fun s₁ o₁ e₁ => ?_
  have e9 : s₁.gpr .x9 + BitVec.ofNat 64 0 = at' S Layout.oStream := by rw [e₁, H.x19, BitVec.add_zero]
  refine zeroWords_ok (t := .x9) (d := 0) (w := 25) (by decide) ⟨by decide, by decide⟩
    (by rw [e9, o₁.wr]; exact hin) fun s₂ k₂ f₂ b₂ => wp_nil ⟨?_, ?_⟩
  · rw [e9] at f₂
    have k : Keep [.x9, .x14] s s₂ := (o₁.keep.trans k₂).mono (by simp)
    refine ⟨fun r hr h30 => k.gpr r (by revert r; decide), k.sp, k.rd, k.wr, ?_, k.vcs⟩
    rw [o₁.mem] at f₂
    exact f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
  · rw [e9] at b₂
    refine Vector.ext fun i hi => ?_
    simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    refine readW_zero fun j hj => ?_
    have := congrArg (fun l => l.getD (8 * i + j) 0) b₂
    simp only [bytesAt_getD _ _ (show 8 * i + j < 8 * 25 by omega_using [hi, hj])] at this
    rw [addr_add, this]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (show 8 * i + j < 8 * 25 by omega_using [hi, hj])]
    rfl

/-- The message `hashM'` hashes: the strings `xs` (`n` bytes each), then
`M′ = 0 ‖ ctx_len ‖ ctx ‖ M`. -/
def hashMsg (n : Nat) (s : State) (S : Addr) (xs : List Arg) : List Byte :=
  (xs.map fun x => bytesAt s.mem (argVal s x) n).flatten ++ bytesAt s.mem (at' S Layout.oHdr) 2 ++
    bytesAt s.mem (s.gpr .x22) (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat

/-- `hashM' p f xs dst len`: `SHAKE256(x₁ ‖ … ‖ M′, len)` to `dst`. -/
theorem hashM_ok (p : Spec.SlhDsa.Params) (hn : p.n ≤ 32) (v : Proof.Sha3.AArch64.Permutation) {f : Fns}
    (hv : f.keccak = v.callee) {xs : List Arg} {dst : Arg} {len : Nat} {s : State} {S : Addr}
    (H : HashIn p.n s S xs dst len) :
    WP isa (Shake.hashM' p f xs dst len) s fun s' =>
      Kept (hashR s S ++ [⟨argVal s dst, len⟩]) s s' ∧
      bytesAt s'.mem (argVal s dst) len = Spec.Sha3.shake256 (hashMsg p.n s S xs) len := by
  unfold Shake.hashM'
  simp only []
  refine WP.seq (WP.mono (zeroState_ok H.ks) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine pieces_ok (rest := .seq _ _) v hv hn xs 0 s₁ [] (by simpa using H.piecesLen) H.pieces H.ks k₁
    (MlKem.repr_nil z₁) rfl fun s₂ k₂ r₂ => ?_
  rw [List.nil_append] at r₂
  have L₂ : ∀ (ys : List Arg), ((ys.map fun x => bytesAt s.mem (argVal s x) p.n).flatten).length = p.n * ys.length := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [List.map_cons, List.flatten_cons, List.length_append, bytesAt_length, ih,
        List.length_cons, Nat.mul_succ]; omega_using []
  have hk := H.piecesLen
  have g19 : ∀ {t : State} {rs : List Region}, Kept rs s t → t.gpr .x19 = S := fun hk =>
    by rw [hk.cs .x19 (by decide) (by decide), H.ks.x19]
  -- the header
  refine WP.seq (WP.mono (kabs_ok v hv (src := .scr Layout.oHdr) (len := .imm 2) (pos := .imm (p.n * xs.length))
    (show Layout.oHdr < 4096 by decide) (show 2 < 2 ^ 64 by decide)
    (show p.n * xs.length < 2 ^ 64 by omega_using [hk]) (by simp) (by simp) (H.ks.kept k₂) r₂
    (by rw [show argVal s₂ (.imm (p.n * xs.length)) = BitVec.ofNat 64 (p.n * xs.length) from rfl, BitVec.toNat_ofNat,
      L₂, Nat.mod_eq_of_lt (show p.n * xs.length < 2 ^ 64 by omega_using [hk]), Nat.mod_eq_of_lt hk])
    (by rw [show argVal s₂ (.scr Layout.oHdr) = at' S Layout.oHdr by simp only [argVal, g19 k₂]]
        exact H.hdr.kept k₂)) fun s₃ ⟨k₃, r₃, x₃⟩ => ?_)
  rw [show argVal s₂ (.scr Layout.oHdr) = at' S Layout.oHdr by simp only [argVal, g19 k₂],
    show (argVal s₂ (.imm 2)).toNat = 2 from rfl, H.hdr.bytes k₂.frame (by decide)] at r₃
  rw [show (argVal s₂ (.imm 2)).toNat = 2 from rfl] at x₃
  have K₃ := kept_trans k₂ k₃
  -- `ctx`
  have e22 : s₃.gpr .x22 = s.gpr .x22 := K₃.cs .x22 (by decide) (by decide)
  have e23 : s₃.gpr .x23 = s.gpr .x23 := K₃.cs .x23 (by decide) (by decide)
  refine WP.seq (WP.mono (kabs_ok v hv (src := .reg .x22) (len := .reg .x23) (pos := .ret)
    (show Reg.x22 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide)
    (show Reg.x23 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide) trivial (by simp) (by simp) (H.ks.kept K₃) r₃
    (by show (s₃.gpr .x0).toNat = _; simp only [x₃, List.length_append, bytesAt_length])
    (by show PieceIn s₃ S (s₃.gpr .x22) (s₃.gpr .x23).toNat
        rw [e22, e23]; exact H.ctx.kept K₃)) fun s₄ ⟨k₄, r₄, x₄⟩ => ?_)
  rw [show argVal s₃ (.reg .x22) = s.gpr .x22 from e22, show argVal s₃ (.reg .x23) = s.gpr .x23 from e23,
    H.ctx.bytes K₃.frame (by have := (s.gpr .x23).isLt; omega_using [this])] at r₄
  rw [show argVal s₃ (.reg .x23) = s.gpr .x23 from e23] at x₄
  have K₄ := kept_trans K₃ k₄
  -- `M`
  have e20 : s₄.gpr .x20 = s.gpr .x20 := K₄.cs .x20 (by decide) (by decide)
  have e21 : s₄.gpr .x21 = s.gpr .x21 := K₄.cs .x21 (by decide) (by decide)
  refine WP.seq (WP.mono (kabs_ok v hv (src := .reg .x20) (len := .reg .x21) (pos := .ret)
    (show Reg.x20 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide)
    (show Reg.x21 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide) trivial (by simp) (by simp) (H.ks.kept K₄) r₄
    (by show (s₄.gpr .x0).toNat = _; simp only [x₄, List.length_append, bytesAt_length])
    (by show PieceIn s₄ S (s₄.gpr .x20) (s₄.gpr .x21).toNat
        rw [e20, e21]; exact H.msg.kept K₄)) fun s₅ ⟨k₅, r₅, x₅⟩ => ?_)
  rw [show argVal s₄ (.reg .x20) = s.gpr .x20 from e20, show argVal s₄ (.reg .x21) = s.gpr .x21 from e21,
    H.msg.bytes K₄.frame (by have := (s.gpr .x21).isLt; omega_using [this])] at r₅
  rw [show argVal s₄ (.reg .x21) = s.gpr .x21 from e21] at x₅
  have K₅ := kept_trans K₄ k₅
  -- the padding
  refine WP.seq (WP.mono (kpad_ok v hv (pos := .ret) trivial (H.ks.kept K₅) r₅
    (by show (s₅.gpr .x0).toNat = _; simp only [x₅, List.length_append, bytesAt_length])) fun s₆ ⟨k₆, z₆⟩ => ?_)
  have K₆ := kept_trans K₅ k₆
  -- the squeeze
  have ed : argVal s₆ dst = argVal s dst := argVal_kept K₆ H.dstA
  refine WP.mono (ksqz_ok v hv (dst := dst) (len := len) H.dstA.ok H.dstA.ne H.len (H.ks.kept K₆)
    (by rw [ed]; exact ⟨H.dst.dst, H.dst.dwk,
      (show MlKem.AArch64.stk s₆ = MlKem.AArch64.stk s by simp only [MlKem.AArch64.stk, K₆.sp]) ▸ H.dst.stk,
      by rw [K₆.wr]; exact H.dst.cov⟩)) fun s' ⟨k', b'⟩ => ⟨?_, ?_⟩
  · rw [ed, K₆.sp] at k'
    refine (K₆.mono fun r hr => List.mem_append_left _ hr).trans (k'.mono fun r hr => ?_)
    simp only [hashR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]
  · rw [← ed, b', z₆, ← MlKem.shake256_eq]
    simp only [hashMsg, List.append_assoc]

/-! ## Constant time

The moves of a call's arguments access no memory, so leak nothing; a call
of a sponge function leaks the same in two runs whose arguments agree. -/

/-- The instructions the moves of arguments are made of. -/
def moveInstr : Instr → Bool
  | .addImm .x _ _ _ | .movz .x _ _ _ | .movk .x _ _ _ | .add .x _ _ _ => true
  | _ => false

theorem moveInstr_addrs {i : Instr} (h : moveInstr i = true) (s : State) : isa.addrs i s = [] := by
  cases i <;> first | rfl | simp [moveInstr] at h

theorem movV_moves (d : Reg) (v : Nat) : (movV d v).all moveInstr = true := by
  unfold movV
  rw [List.all_cons]
  refine Bool.and_eq_true_iff.mpr ⟨rfl, List.all_eq_true.mpr fun i hi => ?_⟩
  obtain ⟨h, _, e⟩ := List.mem_filterMap.mp hi
  split at e <;> cases e; rfl

theorem argMov_moves (d : Reg) (a : Arg) : (a.mov d).all moveInstr = true := by
  cases a with
  | reg r => rfl
  | scr o =>
    simp only [Arg.mov, lea]
    split
    · rfl
    · rw [List.all_append, movV_moves]; rfl
  | imm v => exact movV_moves d v
  | ret => rfl

/-- A block of moves leaks nothing. -/
theorem moves_ct {is : List Instr} (h : is.all moveInstr = true) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_rel (M := isa) (R := fun _ _ => True) (p := moveInstr)
    (fun i hi _ _ _ _ _ _ _ => ⟨trivial, by rw [moveInstr_addrs hi, moveInstr_addrs hi]⟩) is h _ _ _ _ _ _ trivial
    e₁ e₂).2, trivial⟩

/-- The moves of the arguments `as` (none `ret`, into distinct registers of
`x0`–`x5`). -/
theorem moves_ok {is : List Instr} {Q : State → Prop} :
    ∀ (as : List (Reg × Arg)) (s : State), (∀ a ∈ as, ArgOk a.2 ∧ a.2 ≠ .ret ∧ a.1 ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5]) →
      (as.map (·.1)).Nodup →
      (∀ s', Only (as.map (·.1)) s s' → (∀ a ∈ as, s'.gpr a.1 = argVal s a.2) → WP isa (.block is) s' Q) →
      WP isa (.block (as.flatMap (fun (d, a) => a.mov d) ++ is)) s Q
  | [], s, _, _, k => k s (Only.refl _ _) fun _ h => absurd h List.not_mem_nil
  | (d, a) :: as, s, h, hnd, k => by
    simp only [List.flatMap_cons, List.append_assoc]
    obtain ⟨ha, har, hd⟩ := h (d, a) List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine argMov_ok (d := d) ha fun s₁ o₁ e₁ => moves_ok as s₁ (fun x hx => h x (List.mem_cons_of_mem _ hx)) hnd.2
      fun s' o' v' => k s' ((o₁.trans o').mono (by simp)) fun x hx => ?_
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [o'.get _ hnd.1, e₁]
    · obtain ⟨hxa, hxr, hxd⟩ := h x (List.mem_cons_of_mem _ hx)
      rw [v' x hx]
      exact argVal_of_only o₁ hxa (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
        (fun e => by simp only [List.mem_singleton] at e; rw [← e] at hd; simp at hd) hxr

/-- What the moves of an absorb's arguments leave. -/
structure AbsArgs (s : State) (S : Addr) (src len pos : Arg) (s' : State) : Prop where
  only : Only [.x2, .x0, .x1, .x3, .x4, .x5] s s'
  x0 : s'.gpr .x0 = at' S Layout.oStream
  x1 : s'.gpr .x1 = BitVec.ofNat 64 136
  x2 : s'.gpr .x2 = argVal s pos
  x3 : s'.gpr .x3 = argVal s src
  x4 : s'.gpr .x4 = argVal s len
  x5 : s'.gpr .x5 = at' S (Layout.oStream + 200)

theorem absArgs_ok {src len pos : Arg} (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos) (hsr : src ≠ .ret)
    (hlr : len ≠ .ret) {s : State} {S : Addr} (h19 : s.gpr .x19 = S) :
    WP isa (.block (pos.mov .x2 ++ [(Reg.x0, Arg.scr Layout.oStream), (.x1, .imm 136), (.x3, src), (.x4, len),
      (.x5, .scr (Layout.oStream + 200))].flatMap fun (d, a) => a.mov d)) s (AbsArgs s S src len pos) := by
  rw [← List.append_nil (List.flatMap _ _), ← List.append_assoc]
  rw [List.append_assoc]
  refine argMov_ok (d := .x2) hp fun s₁ o₁ e₁ => moves_ok _ s₁ ?_ (by simp) fun s' o' v' => wp_nil ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact ⟨show Layout.oStream < 4096 by decide, by simp, by decide⟩
    · exact ⟨show 136 < 2 ^ 64 by decide, by simp, by decide⟩
    · exact ⟨hs, hsr, by simp⟩
    · exact ⟨hl, hlr, by simp⟩
    · exact ⟨show Layout.oStream + 200 < 4096 by decide, by simp, by decide⟩
  have g19 : s₁.gpr .x19 = S := by rw [o₁.get .x19 (by simp), h19]
  refine ⟨(o₁.trans o').mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v' (.x0, .scr Layout.oStream) (by simp)]; simp only [argVal, g19]
  · exact v' (.x1, .imm 136) (by simp)
  · rw [o'.get .x2 (by simp), e₁]
  · rw [v' (.x3, src) (by simp)]
    exact argVal_of_only o₁ hs (by decide) (by decide) hsr
  · rw [v' (.x4, len) (by simp)]
    exact argVal_of_only o₁ hl (by decide) (by decide) hlr
  · rw [v' (.x5, .scr (Layout.oStream + 200)) (by simp)]; simp only [argVal, g19]

/-- What two runs of an absorb need: each its own setup, and the arguments agree. -/
structure AbsTwo (S : Addr) (src len pos : Arg) (a b : State) : Prop where
  ka : KS a S
  kb : KS b S
  pa : PieceIn a S (argVal a src) (argVal a len).toNat
  pb : PieceIn b S (argVal b src) (argVal b len).toNat
  qa : (argVal a pos).toNat < 136
  src : argVal a src = argVal b src
  len : argVal a len = argVal b len
  pos : argVal a pos = argVal b pos
  sp : a.sp = b.sp

theorem entry_gpr (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

theorem kabs_ct (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {src len pos : Arg}
    (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos) (hsr : src ≠ .ret) (hlr : len ≠ .ret) {S : Addr}
    {P : State → State → Prop} (hP : ∀ a b, P a b → AbsTwo S src len pos a b) :
    RelCT isa P (Shake.kabs f src len pos) fun _ _ => True := by
  unfold Shake.kabs Shake.callA
  simp only [hv]
  refine RelCT.seq (RelCT.wpDep (moves_ct (by
      rw [List.all_append, argMov_moves]
      simp only [List.flatMap_cons, List.flatMap_nil, List.all_append, argMov_moves, Bool.true_and]
      rfl))
    fun a b h => ⟨absArgs_ok hs hl hp hsr hlr (hP a b h).ka.x19, absArgs_ok hs hl hp hsr hlr (hP a b h).kb.x19⟩) ?_
  refine RelCT.callEx (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    fun a1 b1 ⟨_, a, b, h, m₁, m₂⟩ => ?_
  obtain ⟨ka, kb, pa, pb, qa, esrc, elen, epos, esp⟩ := hP a b h
  have pre : ∀ {t t1 : State}, KS t S → PieceIn t S (argVal t src) (argVal t len).toNat → (argVal t pos).toNat < 136 →
      AbsArgs t S src len pos t1 → Proof.Sha3.absorbAArch64.pre (t1.callEntry.withRegions
        [⟨argVal t src, (argVal t len).toNat⟩] [stR S, wkR S]) := by
    intro t t1 kt pt qt mt
    have k := mt.only.keep
    have c0 : t1.callEntry.gpr .x0 = at' S Layout.oStream := (entry_gpr t1).trans mt.x0
    have c1 : t1.callEntry.gpr .x1 = BitVec.ofNat 64 136 := (entry_gpr t1).trans mt.x1
    have c2 : t1.callEntry.gpr .x2 = argVal t pos := (entry_gpr t1).trans mt.x2
    have c3 : t1.callEntry.gpr .x3 = argVal t src := (entry_gpr t1).trans mt.x3
    have c4 : t1.callEntry.gpr .x4 = argVal t len := (entry_gpr t1).trans mt.x4
    have c5 : t1.callEntry.gpr .x5 = at' S (Layout.oStream + 200) := (entry_gpr t1).trans mt.x5
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5, k.sp]
    exact ⟨trivial, trivial, st_wk S, pt.dst, pt.dwk, kt.sp16, kt.kst, pt.stk, kt.kwk, rate136, by rw [toNat_136]; exact qt⟩
  have cov : ∀ {t t1 : State}, KS t S → PieceIn t S (argVal t src) (argVal t len).toNat →
      AbsArgs t S src len pos t1 → Covers ([⟨argVal t src, (argVal t len).toNat⟩] ++ [stR S, wkR S]) (t1.rd ++ t1.wr) ∧
        Covers [stR S, wkR S] t1.wr := fun kt pt mt => by
    rw [mt.only.rd, mt.only.wr]
    exact ⟨Covers.cons (MlKem.AArch64.Covers.head pt.cov) (Covers.right kt.cov), kt.cov⟩
  refine ⟨_, _, _, _, pre ka pa qa m₁, pre kb pb (by rw [← epos]; exact qa) m₂, ?_,
    (cov ka pa m₁).1, (cov ka pa m₁).2, (cov kb pb m₂).1, (cov kb pb m₂).2⟩
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  rw [entry_gpr a1, entry_gpr b1, entry_gpr a1 (r := .x1), entry_gpr b1 (r := .x1), entry_gpr a1 (r := .x2),
    entry_gpr b1 (r := .x2), entry_gpr a1 (r := .x3), entry_gpr b1 (r := .x3), entry_gpr a1 (r := .x4),
    entry_gpr b1 (r := .x4), entry_gpr a1 (r := .x5), entry_gpr b1 (r := .x5), m₁.x0, m₂.x0, m₁.x1, m₂.x1,
    m₁.x2, m₂.x2, m₁.x3, m₂.x3, m₁.x4, m₂.x4, m₁.x5, m₂.x5, m₁.only.sp, m₂.only.sp]
  exact ⟨rfl, rfl, epos, esrc, elen, rfl, esp⟩

/-- What the moves of the padding's arguments leave. -/
structure PadArgs (s : State) (S : Addr) (pos : Arg) (s' : State) : Prop where
  only : Only [.x2, .x0, .x1, .x3, .x4] s s'
  x0 : s'.gpr .x0 = at' S Layout.oStream
  x1 : s'.gpr .x1 = BitVec.ofNat 64 136
  x2 : s'.gpr .x2 = argVal s pos
  x4 : s'.gpr .x4 = at' S (Layout.oStream + 200)

theorem padArgs_ok {pos : Arg} (hp : ArgOk pos) {s : State} {S : Addr} (h19 : s.gpr .x19 = S) :
    WP isa (.block (pos.mov .x2 ++ [(Reg.x0, Arg.scr Layout.oStream), (.x1, .imm 136), (.x3, .imm 0x1f),
      (.x4, .scr (Layout.oStream + 200))].flatMap fun (d, a) => a.mov d)) s (PadArgs s S pos) := by
  rw [← List.append_nil (List.flatMap _ _), ← List.append_assoc, List.append_assoc]
  refine argMov_ok (d := .x2) hp fun s₁ o₁ e₁ => moves_ok _ s₁ ?_ (by simp) fun s' o' v' => wp_nil ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨show Layout.oStream < 4096 by decide, by simp, by decide⟩
    · exact ⟨show 136 < 2 ^ 64 by decide, by simp, by decide⟩
    · exact ⟨show 0x1f < 2 ^ 64 by decide, by simp, by decide⟩
    · exact ⟨show Layout.oStream + 200 < 4096 by decide, by simp, by decide⟩
  have g19 : s₁.gpr .x19 = S := by rw [o₁.get .x19 (by simp), h19]
  refine ⟨(o₁.trans o').mono (by simp), ?_, ?_, ?_, ?_⟩
  · rw [v' (.x0, .scr Layout.oStream) (by simp)]; simp only [argVal, g19]
  · exact v' (.x1, .imm 136) (by simp)
  · rw [o'.get .x2 (by simp), e₁]
  · rw [v' (.x4, .scr (Layout.oStream + 200)) (by simp)]; simp only [argVal, g19]

theorem kpad_ct (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {pos : Arg}
    (hp : ArgOk pos) {S : Addr} {P : State → State → Prop}
    (hP : ∀ a b, P a b → KS a S ∧ KS b S ∧ (argVal a pos).toNat < 136 ∧ argVal a pos = argVal b pos ∧ a.sp = b.sp) :
    RelCT isa P (Shake.kpad f pos) fun _ _ => True := by
  unfold Shake.kpad Shake.callA
  simp only [hv]
  refine RelCT.seq (RelCT.wpDep (moves_ct (by
      rw [List.all_append, argMov_moves]
      simp only [List.flatMap_cons, List.flatMap_nil, List.all_append, argMov_moves, Bool.true_and]
      rfl))
    fun a b h => ⟨padArgs_ok hp (hP a b h).1.x19, padArgs_ok hp (hP a b h).2.1.x19⟩) ?_
  refine RelCT.callEx (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    fun a1 b1 ⟨_, a, b, h, m₁, m₂⟩ => ?_
  obtain ⟨ka, kb, qa, epos, esp⟩ := hP a b h
  have pre : ∀ {t t1 : State}, KS t S → (argVal t pos).toNat < 136 →
      PadArgs t S pos t1 → Proof.Sha3.padAArch64.pre (t1.callEntry.withRegions [] [stR S, wkR S]) := by
    intro t t1 kt qt mt
    have k := mt.only.keep
    have c0 : t1.callEntry.gpr .x0 = at' S Layout.oStream := (entry_gpr t1).trans mt.x0
    have c1 : t1.callEntry.gpr .x1 = BitVec.ofNat 64 136 := (entry_gpr t1).trans mt.x1
    have c2 : t1.callEntry.gpr .x2 = argVal t pos := (entry_gpr t1).trans mt.x2
    have c4 : t1.callEntry.gpr .x4 = at' S (Layout.oStream + 200) := (entry_gpr t1).trans mt.x4
    simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c4, k.sp]
    exact ⟨trivial, trivial, st_wk S, kt.sp16, kt.kst, kt.kwk, rate136, by rw [toNat_136]; exact qt⟩
  have cov : ∀ {t t1 : State}, KS t S → PadArgs t S pos t1 →
      Covers ([] ++ [stR S, wkR S]) (t1.rd ++ t1.wr) ∧ Covers [stR S, wkR S] t1.wr := fun kt mt => by
    rw [mt.only.rd, mt.only.wr]
    exact ⟨Covers.right kt.cov, kt.cov⟩
  refine ⟨_, _, _, _, pre ka qa m₁, pre kb (by rw [← epos]; exact qa) m₂, ?_,
    (cov ka m₁).1, (cov ka m₁).2, (cov kb m₂).1, (cov kb m₂).2⟩
  simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  rw [entry_gpr a1, entry_gpr b1, entry_gpr a1 (r := .x1), entry_gpr b1 (r := .x1), entry_gpr a1 (r := .x2),
    entry_gpr b1 (r := .x2), entry_gpr a1 (r := .x4), entry_gpr b1 (r := .x4), m₁.x0, m₂.x0, m₁.x1, m₂.x1,
    m₁.x2, m₂.x2, m₁.x4, m₂.x4, m₁.only.sp, m₂.only.sp]
  exact ⟨rfl, rfl, epos, rfl, esp⟩

theorem ksqz_ct (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {dst : Arg} {len : Nat}
    (hd : ArgOk dst) (hdr : dst ≠ .ret) (hl : len < 2 ^ 64) {S : Addr} {P : State → State → Prop}
    (hP : ∀ a b, P a b → KS a S ∧ KS b S ∧ PieceOut a S (argVal a dst) len ∧ PieceOut b S (argVal b dst) len ∧
      argVal a dst = argVal b dst ∧ a.sp = b.sp) :
    RelCT isa P (Shake.ksqz f dst len) fun _ _ => True := by
  unfold Shake.ksqz Shake.callA
  simp only [hv]
  have hz : ArgOk (.imm 0) := show 0 < 2 ^ 64 by decide
  have hl' : ArgOk (.imm len) := hl
  refine RelCT.seq (RelCT.wpDep (moves_ct (by
      rw [List.all_append, argMov_moves]
      simp only [List.flatMap_cons, List.flatMap_nil, List.all_append, argMov_moves, Bool.true_and]
      rfl))
    fun a b h => ⟨absArgs_ok hd hl' hz hdr (by simp) (hP a b h).1.x19,
      absArgs_ok hd hl' hz hdr (by simp) (hP a b h).2.1.x19⟩) ?_
  refine RelCT.callEx (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v) fun a1 b1 ⟨_, a, b, h, m₁, m₂⟩ => ?_
  obtain ⟨ka, kb, oa, ob, edst, esp⟩ := hP a b h
  have e4 : (argVal a (.imm len)).toNat = len := by simp only [argVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  have pre : ∀ {t t1 : State}, KS t S → PieceOut t S (argVal t dst) len →
      AbsArgs t S dst (.imm len) (.imm 0) t1 → Proof.Sha3.squeezeAArch64.pre (t1.callEntry.withRegions []
        [stR S, ⟨argVal t dst, len⟩, wkR S]) := by
    intro t t1 kt ot mt
    have k := mt.only.keep
    have c0 : t1.callEntry.gpr .x0 = at' S Layout.oStream := (entry_gpr t1).trans mt.x0
    have c1 : t1.callEntry.gpr .x1 = BitVec.ofNat 64 136 := (entry_gpr t1).trans mt.x1
    have c2 : t1.callEntry.gpr .x2 = BitVec.ofNat 64 0 := (entry_gpr t1).trans mt.x2
    have c3 : t1.callEntry.gpr .x3 = argVal t dst := (entry_gpr t1).trans mt.x3
    have c4 : t1.callEntry.gpr .x4 = BitVec.ofNat 64 len := (entry_gpr t1).trans mt.x4
    have c5 : t1.callEntry.gpr .x5 = at' S (Layout.oStream + 200) := (entry_gpr t1).trans mt.x5
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5, k.sp, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl]
    exact ⟨trivial, trivial, ot.dst, st_wk S, ot.dwk, kt.sp16, kt.kst, ot.stk, kt.kwk, rate136, by decide⟩
  have cov : ∀ {t t1 : State}, KS t S → PieceOut t S (argVal t dst) len → AbsArgs t S dst (.imm len) (.imm 0) t1 →
      Covers ([] ++ [stR S, ⟨argVal t dst, len⟩, wkR S]) (t1.rd ++ t1.wr) ∧
        Covers [stR S, ⟨argVal t dst, len⟩, wkR S] t1.wr := fun {t t1} kt ot mt => by
    rw [mt.only.rd, mt.only.wr]
    have hc : Covers [stR S, ⟨argVal t dst, len⟩, wkR S] t.wr :=
      Covers.cons (MlKem.AArch64.Covers.head kt.cov) (Covers.cons ot.cov (MlKem.AArch64.Covers.tail kt.cov))
    exact ⟨Covers.right hc, hc⟩
  refine ⟨_, _, _, _, pre ka oa m₁, pre kb ob m₂, ?_, (cov ka oa m₁).1, (cov ka oa m₁).2, (cov kb ob m₂).1,
    (cov kb ob m₂).2⟩
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  rw [entry_gpr a1, entry_gpr b1, entry_gpr a1 (r := .x1), entry_gpr b1 (r := .x1), entry_gpr a1 (r := .x2),
    entry_gpr b1 (r := .x2), entry_gpr a1 (r := .x3), entry_gpr b1 (r := .x3), entry_gpr a1 (r := .x4),
    entry_gpr b1 (r := .x4), entry_gpr a1 (r := .x5), entry_gpr b1 (r := .x5), m₁.x0, m₂.x0, m₁.x1, m₂.x1,
    m₁.x2, m₂.x2, m₁.x3, m₂.x3, m₁.x4, m₂.x4, m₁.x5, m₂.x5, m₁.only.sp, m₂.only.sp]
  exact ⟨rfl, rfl, rfl, edst, rfl, rfl, esp⟩

/-! ## `hashM'` in two runs -/

/-- What two runs of the hash agree on: their pointers and lengths. -/
structure HashPub (a b : State) (xs : List Arg) (dst : Arg) : Prop where
  sp : a.sp = b.sp
  x20 : a.gpr .x20 = b.gpr .x20
  x21 : a.gpr .x21 = b.gpr .x21
  x22 : a.gpr .x22 = b.gpr .x22
  x23 : a.gpr .x23 = b.gpr .x23
  pieces : ∀ x ∈ xs, argVal a x = argVal b x
  dst : argVal a dst = argVal b dst

/-- A run of the hash from `σ`, after absorbing `L` bytes (`x0` their
number mod the rate, if `c`). -/
def HI (σ : State) (S : Addr) (L : Nat) (c : Bool) (a : State) : Prop :=
  Kept (hashR σ S) σ a ∧ (∃ msg, Repr a.mem (at' S Layout.oStream) 136 msg ∧ msg.length = L) ∧
    (c = true → (a.gpr .x0).toNat = L % 136)

theorem zeroState_ct {P : State → State → Prop} (hP : ∀ a b, P a b → a.sp = b.sp ∧ a.gpr .x19 = b.gpr .x19) :
    RelCT isa P (.block Shake.zeroState) fun _ _ => True :=
  TreeBase.taintR [.x19] (fun a b h => ⟨(hP a b h).1, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hP a b h).2⟩) (by taint_decide)

/-- One absorb, in two runs from `σ₁` and `σ₂`, then `rest`. -/
theorem kabs_two (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {src len pos : Arg}
    (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos) (hsr : src ≠ .ret) (hlr : len ≠ .ret)
    {σ₁ σ₂ : State} {S : Addr} (K₁ : KS σ₁ S) (K₂ : KS σ₂ S) (esp : σ₁.sp = σ₂.sp) {L : Nat} {c : Bool} {l : Nat}
    (A₁ : PieceIn σ₁ S (argVal σ₁ src) l) (A₂ : PieceIn σ₂ S (argVal σ₂ src) l)
    (hsrc : ∀ {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → Kept (hashR σ S) σ a → argVal a src = argVal σ src)
    (hlen : ∀ {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → Kept (hashR σ S) σ a → argVal a len = BitVec.ofNat 64 l)
    (hpos : ∀ {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → HI σ S L c a → argVal a pos = BitVec.ofNat 64 (L % 136))
    (hl64 : l < 2 ^ 64) (esrc : argVal σ₁ src = argVal σ₂ src) {rest : Prog isa} {Q : State → State → Prop}
    (hr : RelCT isa (fun a b => HI σ₁ S (L + l) true a ∧ HI σ₂ S (L + l) true b) rest Q) :
    RelCT isa (fun a b => HI σ₁ S L c a ∧ HI σ₂ S L c b) (.seq (Shake.kabs f src len pos) rest) Q := by
  have lt : L % 136 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have wp : ∀ {σ : State}, (σ = σ₁ ∨ σ = σ₂) → KS σ S → PieceIn σ S (argVal σ src) l → ∀ a, HI σ S L c a →
      WP isa (Shake.kabs f src len pos) a (HI σ S (L + l) true) := by
    intro σ hσ Kσ Aσ a ⟨ka, ⟨msg, rm, lm⟩, _⟩
    have h := (hlen hσ ka)
    refine WP.mono (kabs_ok v hv hs hl hp hsr hlr (Kσ.kept ka) rm (by rw [hpos hσ ⟨ka, ⟨msg, rm, lm⟩, ‹_›⟩,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt, lm])
      (by rw [hsrc hσ ka, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]; exact Aσ.kept ka)) fun a' ⟨k', r', x'⟩ => ?_
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64] at r' x'
    exact ⟨kept_trans ka k', ⟨_, r', by rw [List.length_append, bytesAt_length, lm]⟩, fun _ => by rw [x', lm]⟩
  refine TreeBase.relSeq (kabs_ct v hv hs hl hp hsr hlr (S := S) fun a b ⟨ha, hb⟩ => ?_) (wp (.inl rfl) K₁ A₁) (wp (.inr rfl) K₂ A₂) hr
  have e₁ := hsrc (.inl rfl) ha.1
  have e₂ := hsrc (.inr rfl) hb.1
  refine ⟨K₁.kept ha.1, K₂.kept hb.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁, hlen (.inl rfl) ha.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]; exact A₁.kept ha.1
  · rw [e₂, hlen (.inr rfl) hb.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64]; exact A₂.kept hb.1
  · rw [hpos (.inl rfl) ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]; exact Nat.mod_lt _ (by decide)
  · rw [e₁, e₂, esrc]
  · rw [hlen (.inl rfl) ha.1, hlen (.inr rfl) hb.1]
  · rw [hpos (.inl rfl) ha, hpos (.inr rfl) hb]
  · rw [ha.1.sp, hb.1.sp, esp]

/-- The absorbs of the strings `ys` in two runs, the first at position `n j`. -/
private theorem pieces_ct (v : Proof.Sha3.AArch64.Permutation) {f : Fns} (hv : f.keccak = v.callee) {n : Nat}
    (hn : n ≤ 32) {σ₁ σ₂ : State} {S : Addr} (K₁ : KS σ₁ S) (K₂ : KS σ₂ S) (esp : σ₁.sp = σ₂.sp) {rest : Prog isa}
    {Q : State → State → Prop} :
    ∀ (ys : List Arg) (j : Nat) (c : Bool), n * (j + ys.length) < 136 →
      (∀ y ∈ ys, PieceArg y ∧ PieceIn σ₁ S (argVal σ₁ y) n ∧ PieceIn σ₂ S (argVal σ₂ y) n ∧
        argVal σ₁ y = argVal σ₂ y) →
      (∀ c', RelCT isa (fun a b => HI σ₁ S (n * (j + ys.length)) c' a ∧ HI σ₂ S (n * (j + ys.length)) c' b) rest Q) →
      RelCT isa (fun a b => HI σ₁ S (n * j) c a ∧ HI σ₂ S (n * j) c b)
        ((ys.zipIdx j).foldr (fun (x, i) c => .seq (Shake.kabs f x (.imm n) (.imm (n * i))) c) rest) Q
  | [], j, c, _, _, hr => by simpa using hr c
  | y :: ys, j, c, hb, hy, hr => by
    rw [List.zipIdx_cons, List.foldr_cons]
    obtain ⟨ya, y₁, y₂, ey⟩ := hy y List.mem_cons_self
    have hj : n * j < 136 := by
      have := Nat.mul_le_mul_left n (show j ≤ j + (y :: ys).length by omega_using [])
      omega_using [hb, this]
    have hn64 : n < 2 ^ 64 := by omega_using [hn]
    refine kabs_two v hv (len := .imm n) (pos := .imm (n * j)) ya.ok (show n < 2 ^ 64 from hn64)
      (show n * j < 2 ^ 64 by omega_using [hj]) ya.ne (by simp)
      K₁ K₂ esp y₁ y₂ (fun _ hk => argVal_kept hk ya) (fun _ _ => rfl)
      (fun _ _ => by simp only [argVal, Nat.mod_eq_of_lt hj]) hn64 ey ?_
    have e : n * j + n = n * (j + 1) := by rw [Nat.mul_succ]
    rw [e]
    refine pieces_ct v hv hn K₁ K₂ esp ys (j + 1) true (by
        simp only [List.length_cons] at hb; rw [show j + 1 + ys.length = j + (ys.length + 1) by omega_using []]; exact hb)
      (fun z hz => hy z (List.mem_cons_of_mem _ hz)) fun c' => ?_
    rw [show j + 1 + ys.length = j + (y :: ys).length by simp only [List.length_cons]; omega_using []]
    exact hr c'

theorem PieceOut.kept {s s' : State} {S a : Addr} {l : Nat} {rs : List Region} (h : PieceOut s S a l)
    (hk : Kept rs s s') : PieceOut s' S a l :=
  ⟨h.dst, h.dwk, (show MlKem.AArch64.stk s' = MlKem.AArch64.stk s by simp only [MlKem.AArch64.stk, hk.sp]) ▸ h.stk,
    by rw [hk.wr]; exact h.cov⟩

/-- `hashM'` in two runs whose pointers and lengths agree. -/
theorem hashM_ct (p : Spec.SlhDsa.Params) (hn : p.n ≤ 32) (v : Proof.Sha3.AArch64.Permutation) {f : Fns}
    (hv : f.keccak = v.callee) {xs : List Arg} {dst : Arg} {len : Nat} {S : Addr} {P : State → State → Prop}
    (hP : ∀ a b, P a b → HashIn p.n a S xs dst len ∧ HashIn p.n b S xs dst len ∧ HashPub a b xs dst) :
    RelCT isa P (Shake.hashM' p f xs dst len) fun _ _ => True := by
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨H₁, H₂, Hp⟩ := hP _ _ hp
  suffices R : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (Shake.hashM' p f xs dst len) fun _ _ => True from
    R _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have K₁ := H₁.ks
  have K₂ := H₂.ks
  have esp := Hp.sp
  have hk := H₁.piecesLen
  unfold Shake.hashM'
  simp only []
  refine TreeBase.relSeq (B₁ := fun a => Kept (hashR σ₁ S) σ₁ a ∧ stateAt a.mem (at' S Layout.oStream) = Spec.Sha3.zero)
    (B₂ := fun a => Kept (hashR σ₂ S) σ₂ a ∧ stateAt a.mem (at' S Layout.oStream) = Spec.Sha3.zero)
    (zeroState_ct fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨esp, by rw [K₁.x19, K₂.x19]⟩)
    (fun a h => by subst h; exact zeroState_ok K₁) (fun b h => by subst h; exact zeroState_ok K₂) ?_
  have hb0 : p.n * (0 + xs.length) < 136 := by rw [Nat.zero_add]; exact hk
  have hpc : ∀ y ∈ xs, PieceArg y ∧ PieceIn σ₁ S (argVal σ₁ y) p.n ∧ PieceIn σ₂ S (argVal σ₂ y) p.n ∧
      argVal σ₁ y = argVal σ₂ y := fun y hy =>
    ⟨(H₁.pieces y hy).1, (H₁.pieces y hy).2, (H₂.pieces y hy).2, Hp.pieces y hy⟩
  have init : ∀ {σ a : State}, Kept (hashR σ S) σ a ∧ stateAt a.mem (at' S Layout.oStream) = Spec.Sha3.zero →
      HI σ S (p.n * 0) false a := fun ⟨k, z⟩ => ⟨k, ⟨[], MlKem.repr_nil z, by simp⟩, nofun⟩
  refine RelCT.mono (pieces_ct v hv hn K₁ K₂ esp xs 0 false hb0 hpc fun c' => ?_)
    (fun a b h => ⟨init h.1, init h.2⟩) fun _ _ h => h
  rw [Nat.zero_add]
  have hk64 : p.n * xs.length < 2 ^ 64 := by omega_using [hk]
  have hdrA : ∀ σ : State, KS σ S → argVal σ (.scr Layout.oHdr) = at' S Layout.oHdr := fun σ K => by
    simp only [argVal, K.x19]
  have hdrP : PieceArg (.scr Layout.oHdr) := show Layout.oHdr < 4096 by decide
  -- the header
  refine kabs_two v hv (src := .scr Layout.oHdr) (len := .imm 2) (pos := .imm (p.n * xs.length)) hdrP.ok
    (show 2 < 2 ^ 64 by decide) hk64 hdrP.ne (by simp) K₁ K₂ esp
    (by rw [hdrA σ₁ K₁]; exact H₁.hdr) (by rw [hdrA σ₂ K₂]; exact H₂.hdr) (fun _ hk' => argVal_kept hk' hdrP)
    (fun _ _ => rfl) (fun _ _ => by simp only [argVal, Nat.mod_eq_of_lt hk]) (by decide)
    (by rw [hdrA σ₁ K₁, hdrA σ₂ K₂]) ?_
  -- `ctx`
  have hx22 : PieceArg (.reg .x22) := ⟨by decide, by decide, by decide⟩
  have hx23 : ∀ {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → Kept (hashR σ S) σ a →
      argVal a (.reg .x23) = BitVec.ofNat 64 (σ₁.gpr .x23).toNat := fun {σ a} hσ hk' => by
    show a.gpr .x23 = _
    rw [hk'.cs .x23 (by decide) (by decide), ← ofNat_of_toNat rfl]
    rcases hσ with rfl | rfl
    · rfl
    · exact Hp.x23.symm
  have hret : ∀ {L : Nat} {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → HI σ S L true a →
      argVal a .ret = BitVec.ofNat 64 (L % 136) := fun _ h => ofNat_of_toNat (h.2.2 rfl)
  refine kabs_two v hv (src := .reg .x22) (len := .reg .x23) (pos := .ret) hx22.ok (show Reg.x23 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide) trivial hx22.ne (by simp)
    K₁ K₂ esp H₁.ctx (by rw [Hp.x23]; exact H₂.ctx) (fun _ hk' => argVal_kept hk' hx22) hx23 hret
    (σ₁.gpr .x23).isLt Hp.x22 ?_
  -- `M`
  have hx20 : PieceArg (.reg .x20) := ⟨by decide, by decide, by decide⟩
  have hx21 : ∀ {σ a : State}, (σ = σ₁ ∨ σ = σ₂) → Kept (hashR σ S) σ a →
      argVal a (.reg .x21) = BitVec.ofNat 64 (σ₁.gpr .x21).toNat := fun {σ a} hσ hk' => by
    show a.gpr .x21 = _
    rw [hk'.cs .x21 (by decide) (by decide), ← ofNat_of_toNat rfl]
    rcases hσ with rfl | rfl
    · rfl
    · exact Hp.x21.symm
  refine kabs_two v hv (src := .reg .x20) (len := .reg .x21) (pos := .ret) hx20.ok (show Reg.x21 ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5] by decide) trivial hx20.ne (by simp)
    K₁ K₂ esp H₁.msg (by rw [Hp.x21]; exact H₂.msg) (fun _ hk' => argVal_kept hk' hx20) hx21 hret
    (σ₁.gpr .x21).isLt Hp.x20 ?_
  -- the padding and the squeeze
  generalize p.n * xs.length + 2 + (σ₁.gpr .x23).toNat + (σ₁.gpr .x21).toNat = L
  have wpad : ∀ {σ : State}, (σ = σ₁ ∨ σ = σ₂) → KS σ S → ∀ a, HI σ S L true a →
      WP isa (Shake.kpad f .ret) a (fun a' => Kept (hashR σ S) σ a') := fun hσ K a ⟨ka, ⟨msg, rm, lm⟩, xa⟩ =>
    WP.mono (kpad_ok v hv (pos := .ret) trivial (K.kept ka) rm (by show (a.gpr .x0).toNat = _; rw [xa rfl, lm]))
      fun a' ⟨k', _⟩ => kept_trans ka k'
  refine TreeBase.relSeq (kpad_ct v hv (pos := .ret) trivial (S := S) fun a b ⟨ha, hb⟩ =>
      ⟨K₁.kept ha.1, K₂.kept hb.1, (by rw [hret (.inl rfl) ha, BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))),
        by rw [hret (.inl rfl) ha, hret (.inr rfl) hb], by rw [ha.1.sp, hb.1.sp, esp]⟩)
    (wpad (.inl rfl) K₁) (wpad (.inr rfl) K₂) ?_
  refine ksqz_ct v hv H₁.dstA.ok H₁.dstA.ne H₁.len (S := S) fun a b ⟨ha, hb⟩ => ?_
  rw [argVal_kept ha H₁.dstA, argVal_kept hb H₁.dstA]
  exact ⟨K₁.kept ha, K₂.kept hb, H₁.dst.kept ha, H₂.dst.kept hb, Hp.dst, by rw [ha.sp, hb.sp, esp]⟩

end VG.Proof.SlhDsa.AArch64
