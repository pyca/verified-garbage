module

public import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: K-PKE.Encrypt, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/Encrypt.lean`). `K.encrypt` runs within
encapsulation and decapsulation, on buffers the callers choose (`EB`): the
encapsulation key (in `s10`), the message (in `s9`) and the ciphertext (in
`s7`), each at an offset of one of the callers' buffers; `r` is at 952 in
`scratch`. It writes the ciphertext, and changes nothing but the regions of
`encW` (`encrypt_ok`). Its phases: `ρ` copied to the seed of `SampleNTT`,
`t̂` decoded (`decT_loop`), the `PRF`s into `ŷ`, `e₁` and `e₂`, `μ`, the rows
of `u` compressed into the ciphertext (`encRow_step`), and `v`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-! ## Regions inside regions -/

theorem sepB_mono {sz : List Nat} {a a' b b' : Nat × Nat × Nat} (h : sepB sz a b = true) (ha : inB a' a = true)
    (hb : inB b' b = true) : sepB sz a' b' = true := by
  obtain ⟨i, o, l⟩ := a
  obtain ⟨i', o', l'⟩ := a'
  obtain ⟨j, p, n⟩ := b
  obtain ⟨j', p', n'⟩ := b'
  simp only [inB, sepB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h ha hb ⊢
  obtain ⟨⟨e1, a1⟩, a2⟩ := ha
  obtain ⟨⟨e2, b1⟩, b2⟩ := hb
  subst e1; subst e2
  omega_arith

theorem sepAll_mono {sz : List Nat} {a a' : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W' = true) (ha : inB a' a = true) (hW : W.all (fun w => W'.any (inB w)) = true) :
    sepAll sz a' W = true :=
  List.all_eq_true.mpr fun w hw => by
    obtain ⟨w', hw', hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hW w hw)
    exact sepB_mono (List.all_eq_true.mp h w' hw') ha hi

theorem inB_off {i o l k n : Nat} (h : k + n ≤ l) : inB (i, o + k, n) (i, o, l) = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega_arith

theorem inB_refl (w : Nat × Nat × Nat) : inB w w = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega_arith

/-- The bounds of a region apart from another. -/
theorem sepAll_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz (i, o, l) (w :: W) = true) : i < sz.length ∧ o + l ≤ sz.getD i 0 :=
  sepB_bounds (List.all_eq_true.mp h w (List.mem_cons_self ..))

/-! ## Copying from an offset -/

theorem copyLo {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {bo so dO len i j : Nat}
    (hdb : db ∈ preserved) (hsb : sb ≠ .a0) (gs : s.gpr sb = L.A i bo) (gd : s.gpr db = L.ptr j)
    (hse : so < 32768) (hde : dO < 32768) (hle : len < 2048) (hl0 : 0 < len)
    (hs : sepB L.sizes (i, bo + so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i (bo + so)) len := by
  refine WP.seq (WP.mono (copy_setup hdb hsb hse hde hle) fun s₁ ⟨o₁, g3, g4, g5⟩ => ?_)
  rw [gs, ptr_add] at g3; rw [gd] at g4
  refine WP.mono (copy_loop (by omega_arith) hl0 (Lay.disj hL hs)
    (by rw [o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g3 g4 g5)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨(o₁.kept _).trans ⟨cs, sp, rd, wr, fr⟩, ?_⟩
  rw [o₁.mem] at hb; exact hb

/-! ## Products with constants -/

theorem mul_eq (p : BitVec 64) (m i : Nat) : p + BitVec.ofNat 64 i * BitVec.ofNat 64 m = p + BitVec.ofNat 64 (m * i) := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- `d ← b + m c`, through `t0`. -/
theorem atMul_ok {s : State} {d b c : Reg} {m : Nat} (hb : b ≠ .t0) (hc : c ≠ .t0)
    (hm : m < 2048) :
    WP isa (.block (atMul d b c m)) s fun s' =>
      s'.gpr d = s.gpr b + s.gpr c * BitVec.ofNat 64 m ∧ (∀ r, r ≠ d → r ≠ .t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [← List.append_nil (atMul d b c m)]
  exact wp_atMul hm hb hc fun s' u => WP.block_nil ⟨u.gpr, u.other, u.mem, u.rd, u.wr, u.sp⟩

/-! ## Decoding `t̂` -/

theorem decTArgs_ok {s : State} {P B : BitVec 64} {i : Nat} (hi : i < 2048) (h11 : s.gpr .s11 = P)
    (h10 : s.gpr .s10 = B) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) :
    WP isa (.block (atMul .a0 .s10 .s6 384 ++ slotAt .a1 .s6 0)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = B + BitVec.ofNat 64 (384 * i) ∧
      s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly i) := by
  rw [← List.append_nil (slotAt .a1 .s6 0)]
  refine wp_atMul (by decide) (by decide) (by decide) fun s₁ u₁ =>
    wp_slotAt (i := i) (by decide) (by omega) (by decide) (by rw [u₁.other _ (by decide) (by decide), h6])
      fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
        by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩, ?_, ?_⟩
  · obtain ⟨n0, n1, n2, -, -, -⟩ := pres_ne hr
    rw [u₂.other _ n2, u₁.other _ n1 n0]
  · rw [u₂.other _ (by decide), u₁.gpr, h10, h6, mul_eq]
  · rw [u₂.gpr, u₁.other _ (by decide) (by decide), h11]

/-- The polynomials `0` to `k - 1` decoded from the `384 k` bytes at offset `o` of buffer `i` (in `r30`). -/
structure DecInv (K : KemLay) (L : Lay) (i o : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s6] (L.RL [(0, 2048, 1024 * K.k)]) s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 j
  t : ∀ k < j, PolyIs s.mem (L.A 0 (oPoly k)) (decode12 (bytesAt s₀.mem (L.A i (o + 384 * k)) 384))

/-- Polynomial `k < K.k` of `t̂` is in what the decoding writes, apart from the others. -/
abbrev DecTSlots (K : KemLay) : Prop :=
  ∀ k < K.k, [((0 : Nat), oPoly k, (1024 : Nat))].all (fun w => [(0, 2048, 1024 * K.k)].any (subB0 w)) = true ∧
    (∀ k' < K.k, k' ≠ k → [((0 : Nat), oPoly k, (1024 : Nat))].all (sep0 (oPoly k') 1024) = true)

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem decT_slots : DecTSlots K := (by decide : ∀ k < 5, DecTSlots (kOf k)) K.k (by have := hK.k4; omega_arith)

theorem decT_step {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h30 : s₀.gpr .s10 = L.A i o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr)
    {j : Nat} (hj : j < K.k) {s : State} (h : DecInv K L i o s₀ j s) :
    WP isa K.decTBody s fun s' => DecInv K L i o s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hc' := h.kx.ctx (by decide) hc
  obtain ⟨c_sub, c_sep⟩ := decT_slots hK j hj
  have g30 : s.gpr .s10 = L.A i o := by rw [h.kx.cs .s10 (by decide) (by decide), h30]
  refine WP.seq (WP.mono (decTArgs_ok (by omega) hc'.s11 g30 h.s6) fun s₁ ⟨o₁, a3, a4⟩ => ?_)
  rw [ptr_add] at a3
  have hc₁ := hc'.only o₁
  have hsj : sepAll L.sizes (i, o + 384 * j, 384) [(0, 2048, 1024 * K.k)] = true :=
    sepAll_mono hs (inB_off (by omega_arith)) (by kdecide)
  have hsep : sepB L.sizes (i, o + 384 * j, 384) (0, oPoly j, 1024) = true :=
    sepB_mono (List.all_eq_true.mp hsj _ (List.mem_singleton_self _)) (inB_refl _) (by
      simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega_arith)
  refine WP.seq (decode12L hL a3 a4 hsep (by rw [o₁.rd, o₁.wr, h.kx.rd, h.kx.wr]; exact hr) hc₁.cw
    (hc.alP j) fun s₂ k₂ p₂ => ?_)
  have g26 : s₂.gpr .s6 = BitVec.ofNat 64 j := by
    rw [k₂.cs .s6 (by decide), o₁.cs .s6 (by decide), h.s6]
  refine WP.mono (count_ok (by decide) (by omega_arith) (by omega_arith) g26) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
  all_goals have K : KeptX [.s6] (L.RL [(0, oPoly j, 1024)]) s s' :=
    (o₁.x _ _).trans ((k₂.x _).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))
  · exact h.kx.trans (K.subL hc c_sub)
  · intro k hk
    have hb : bytesAt s.mem (L.A i (o + 384 * j)) 384 = bytesAt s₀.mem (L.A i (o + 384 * j)) 384 :=
      Lay.bytes_keep hL h.kx.frame hsj (by decide)
    by_cases e : k = j
    · subst e
      rw [o₁.mem, hb] at p₂
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₂
    · exact Lay.polyIs_keep hL K.frame (hc.sepAll0 (by offs) (c_sep k (by omega_arith) e)) (h.t k (by omega_arith))

omit hK in
theorem decT_init {L : Lay} {i o : Nat} {s₀ : State} :
    WP isa (.block [.li .s6 0]) s₀ (DecInv K L i o s₀ 0) :=
  WP.mono (li_ok .s6 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem decT_loop {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h30 : s₀.gpr .s10 = L.A i o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr) {s : State}
    (h : DecInv K L i o s₀ 0 s) : WP isa (.loop K.decTBody (.nonzero .t0)) s (DecInv K L i o s₀ K.k) :=
  wp_loop_nz (DecInv K L i o s₀) (N := K.k) (by have := hK.k1; omega_arith)
    (fun _ hj _ h => decT_step hK hc h30 hs hr hj h) (fun _ h => h) h

end

namespace Enc

/-! ## The buffers of K-PKE.Encrypt -/

/-- Where `encrypt` finds `ek` and `m`, and writes `c`: offsets in buffers. -/
structure EB where
  iE : Nat
  oE : Nat
  iM : Nat
  oM : Nat
  iC : Nat
  oC : Nat

/-- What `encrypt` changes in `scratch` and the stack: the polynomials and the
working spaces of the callees. -/
abbrev encW0 (K : KemLay) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 984, 1), (0, 1056, 128), (0, 1248, 34), (0, 2048, 1024 * (3 * K.k + 5)), (0, K.oSample, 3072),
    (1, 0, 1168)]

/-- What `encrypt` changes. -/
abbrev encW (K : KemLay) (b : EB) : List (Nat × Nat × Nat) := encW0 K ++ [(b.iC, b.oC, K.ctLen)]

/-- A state `encrypt` runs from. -/
structure EncPre (K : KemLay) (L : Lay) (b : EB) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  ctx : Ctx L s
  s10 : s.gpr .s10 = L.A b.iE b.oE
  s9 : s.gpr .s9 = L.A b.iM b.oM
  s7 : s.gpr .s7 = L.A b.iC b.oC
  sE : sepAll L.sizes (b.iE, b.oE, K.ekLen) (encW0 K) = true
  sM : sepAll L.sizes (b.iM, b.oM, 32) (encW0 K) = true
  sC : sepAll L.sizes (b.iC, b.oC, K.ctLen) (encW0 K) = true
  wE : L.buf b.iE ∈ s.rd ++ s.wr
  wM : L.buf b.iM ∈ s.rd ++ s.wr
  wC : L.buf b.iC ∈ s.wr

/-- The entries of `Â` the products use, from `ρ` and `r`: `Â[i, j]`, or
`ŷ[i]` if its `SampleNTT` does not finish. -/
def aEnc (ρ r : List Byte) (i j : Nat) : Poly := effA true ρ j i (VG.Proof.MlKem.encY r i)

/-- Whether the `SampleNTT`s of the first `i` rows of `Â^⊺` (of `k` entries) finished. -/
def okEnc (k : Nat) (ρ : List Byte) (i : Nat) : Bool := (List.range i).all fun i' => okRow true ρ i' k

section
variable (K : KemLay) (L : Lay) (b : EB) (s₀ : State)

/-- `ek`. -/
abbrev ekB : List Byte := bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen
/-- `m`. -/
abbrev mB : List Byte := bytesAt s₀.mem (L.A b.iM b.oM) 32
/-- `r`. -/
abbrev rB : List Byte := bytesAt s₀.mem (L.A 0 oSigma) 32

/-- `ρ`. -/
abbrev ρE : List Byte := ekRho K.p (ekB K L b s₀)
/-- The entries of `Â` the products use. -/
abbrev aE : Nat → Nat → Poly := aEnc (ρE K L b s₀) (rB L s₀)
/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
abbrev okE (i : Nat) : Bool := okEnc K.k (ρE K L b s₀) i

end

theorem okE_succ (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) :
    okE K L b s₀ (i + 1) = (okE K L b s₀ i && okRow true (ρE K L b s₀) i K.k) := by
  simp only [okE, okEnc, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Before the rows: what changes is within `encW0`. -/
abbrev EA (K : KemLay) (L : Lay) (s₀ s : State) : Prop := KeptX [.s6, .s5, .s4] (L.RL (encW0 K)) s₀ s

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem EA.ctx {s : State} (h : EA K L s₀ s) : Ctx L s := KeptX.ctx h (by decide) hp.ctx

/-- The bytes of a part of a buffer apart from `encW0`. -/
theorem EA.bytes {s : State} (h : EA K L s₀ s) {i o l : Nat} (hs : sepAll L.sizes (i, o, l) (encW0 K) = true) :
    bytesAt s.mem (L.A i o) l = bytesAt s₀.mem (L.A i o) l := by
  have := sepAll_bounds hs
  have := hp.ctx.ok.fit i this.1
  exact Lay.bytes_keep hp.ctx.ok h.frame hs (by simp only [Lay.size] at this; omega_arith)

theorem EA.ek {s : State} (h : EA K L s₀ s) {k n : Nat} (hk : k + n ≤ K.ekLen) :
    bytesAt s.mem (L.A b.iE (b.oE + k)) n = bytesAt s₀.mem (L.A b.iE (b.oE + k)) n :=
  EA.bytes hp h (sepAll_mono hp.sE (inB_off hk)
    (List.all_eq_true.mpr fun _ h => List.any_eq_true.mpr ⟨_, h, inB_refl _⟩))

omit hp in
theorem EA.reg {s : State} (h : EA K L s₀ s) {r : Reg} (hr : r ∈ [Reg.s10, .s9, .s11, .s7]) :
    s.gpr r = s₀.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact h.cs _ (by decide) (by decide)

/-! ## `ρ` -/

theorem enc1_ok : WP isa (copy .s10 (384 * K.k) .s11 oSeed 32) s₀ fun s =>
    EA K L s₀ s ∧ Frame (L.RL [(0, oSeed, 32)]) s₀.mem s.mem ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  have hs : sepB L.sizes (b.iE, b.oE + 384 * K.k, 32) (0, oSeed, 32) = true :=
    sepB_mono (List.all_eq_true.mp hp.sE (0, 1248, 34) (by simp)) (inB_off (by offs)) (by decide)
  refine WP.mono (copyLo hL (bo := b.oE) (by decide) (by decide) hp.s10 hp.ctx.s11 (by offs)
    (by decide) (by decide) (by decide) hs hp.wE hp.ctx.cw) fun s ⟨k, e⟩ =>
    ⟨(k.x _).subL hp.ctx (by kdecide), k.frame, e.trans ?_⟩
  show _ = ((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * K.k)).take 32
  rw [bytesAt_slice _ _ (by offs), ptr_add]

/-! ## `t̂` -/

theorem enc2_ok {s₁ : State} (h₁ : EA K L s₀ s₁) (hρ : bytesAt s₁.mem (L.A 0 oSeed) 32 = ρE K L b s₀) {s : State}
    (h : DecInv K L b.iE b.oE s₁ K.k s) :
    EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      ∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k) := by
  have hK := hp.wf
  refine ⟨h₁.trans ((h.kx.weaken (by simp)).subL hp.ctx (by kdecide)),
    (Lay.bytes_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans hρ,
    fun k hk => ?_⟩
  have := h.t k hk
  rw [EA.ek hp h₁ (by offs)] at this
  show PolyIs _ _ (decode12 (((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * k)).take 384))
  rw [bytesAt_slice _ _ (by offs), ptr_add]; exact this

/-! ## The `PRF`s -/

/-- How the regions of the `PRF`s lie among those of `encrypt`. -/
abbrev PrfEk (K : KemLay) : Prop := (prfLW K 0 K.k).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (prfLW K K.k (2 * K.k + 1)).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (prfLW K 0 K.k).all (sep0 oSeed 32) = true ∧ (prfLW K K.k (2 * K.k + 1)).all (sep0 oSeed 32) = true ∧
    (∀ k < K.k, (prfLW K 0 K.k).all (sep0 (oPoly k) 1024) = true) ∧
    (∀ k < 2 * K.k, (prfLW K K.k (2 * K.k + 1)).all (sep0 (oPoly k) 1024) = true) ∧
    (encW0 K).all (sep0 oSigma 32) = true

omit hp in
theorem prf_ek (hK : K.WF) : PrfEk K :=
  (by decide : ∀ k < 5, PrfEk (kOf k)) K.k (by have := hK.k4; omega_arith)

theorem enc3_ok {s₂ : State} (h₂ : EA K L s₀ s₂) (hρ : bytesAt s₂.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (ht : ∀ k < K.k, PolyIs s₂.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) :
    WP isa (K.prfLoop true 0 K.k) s₂ fun s => EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      (∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) ∧
      ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₂
  obtain ⟨c1, -, c3, -, c5, -, c7⟩ := prf_ek hK
  refine WP.mono (prfLoop_ok hK hc true (N₀ := 0) (N₁ := K.k) (by have := hK.k1; omega_arith) (by omega_arith)
    (EA.bytes hp h₂ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ =>
    ⟨?_, ?_, fun k' hk' => ?_, fun j hj => ?_⟩
  · exact h₂.trans ((k.weaken (by simp)).subL hp.ctx c1)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c3) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c5 k' hk')) (ht k' hk')
  · exact p j (Nat.zero_le _) hj

theorem enc4_ok {s₃ : State} (h₃ : EA K L s₀ s₃) (hρ : bytesAt s₃.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (hv : ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))) :
    WP isa (K.prfLoop false K.k (2 * K.k + 1)) s₃ fun s => EA K L s₀ s ∧
      bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      (∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
        else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))) ∧
      ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
        PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₃
  obtain ⟨-, c2, -, c4, -, c6, c7⟩ := prf_ek hK
  refine WP.mono (prfLoop_ok hK hc false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega_arith) (by omega_arith)
    (EA.bytes hp h₃ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, p⟩
  · exact h₃.trans ((k.weaken (by simp)).subL hp.ctx c2)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c4) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c6 k' hk')) (hv k' hk')

/-! ## `μ` -/

omit hp in
theorem muArgs_ok (hK : K.WF) {s : State} {P M : BitVec 64} (h11 : s.gpr .s11 = P) (h9 : s.gpr .s9 = M) :
    WP isa (.block ([mov .a0 .s9, .li .a1 32, .li .a2 1] ++ polyAddr .a3 (3 * K.k + 1))) s
      fun s' => Only s s' ∧ s'.gpr .a0 = M ∧ s'.gpr .a1 = BitVec.ofNat 64 (32 * 1) ∧
        s'.gpr .a2 = BitVec.ofNat 64 1 ∧ s'.gpr .a3 = P + BitVec.ofNat 64 (oPoly (3 * K.k + 1)) := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .a3 (3 * K.k + 1))]
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ h₁ => wp_li (by decide) fun s₂ h₂ => wp_li (by decide) fun s₃ h₃ =>
    wp_polyAddr (by omega) (by decide) fun s₄ h₄ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
        (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h9]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), h11]

theorem enc5a_ok {s₄ : State} (h₄ : EA K L s₀ s₄) :
    WP isa (.block ([mov .a0 .s9, .li .a1 32, .li .a2 1] ++ polyAddr .a3 (3 * K.k + 1))) s₄
      fun s => (EA K L s₀ s ∧ s.mem = s₄.mem) ∧ s.gpr .a0 = L.A b.iM b.oM ∧
        s.gpr .a1 = BitVec.ofNat 64 (32 * 1) ∧ s.gpr .a2 = BitVec.ofNat 64 1 ∧
        s.gpr .a3 = L.A 0 (oPoly (3 * K.k + 1)) := by
  have hc := EA.ctx hp h₄
  have g29 : s₄.gpr .s9 = L.A b.iM b.oM := by rw [EA.reg h₄ (by simp), hp.s9]
  exact WP.mono (muArgs_ok hp.wf hc.s11 g29) fun s₁ ⟨o₁, a3, a4, a5, a6⟩ =>
    ⟨⟨h₄.trans (o₁.x _ _), o₁.mem⟩, a3, a4, a5, a6⟩

theorem enc5b_ok {s₄ s : State} (h₄ : EA K L s₀ s₄) (h : EA K L s₀ s ∧ s.mem = s₄.mem)
    (a3 : s.gpr .a0 = L.A b.iM b.oM) (a4 : s.gpr .a1 = BitVec.ofNat 64 (32 * 1))
    (a5 : s.gpr .a2 = BitVec.ofNat 64 1) (a6 : s.gpr .a3 = L.A 0 (oPoly (3 * K.k + 1))) :
    WP isa callDecompress s fun s' => EA K L s₀ s' ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s'.mem ∧
      PolyIs s'.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀)) := by
  have hK := hp.wf
  have hc := EA.ctx hp h.1
  have hs : sepB L.sizes (b.iM, b.oM, 32 * 1) (0, oPoly (3 * K.k + 1), 1024) = true :=
    sepB_mono (List.all_eq_true.mp hp.sM (0, 2048, 1024 * (3 * K.k + 5)) (by simp)) (inB_refl _) (by kdecide)
  refine decompressL hp.ctx.ok a3 a4 a5 a6 (by decide) hs (by rw [h.1.rd, h.1.wr]; exact hp.wM)
    hc.cw (hc.alP _) fun s' k p => ⟨?_, ?_, ?_⟩
  · exact h.1.trans ((k.x _).subL hp.ctx (by kdecide))
  · rw [← h.2]; exact k.frame
  · rw [h.2, show 32 * 1 = 32 from rfl, EA.bytes hp h₄ hp.sM] at p; exact p

end

/-! ## What the rows and `v` use -/

theorem sepAll_left {sz : List Nat} {a a' : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)} (h : sepAll sz a W = true)
    (ha : inB a' a = true) : sepAll sz a' W = true :=
  sepAll_mono h ha (List.all_eq_true.mpr fun w hw => List.any_eq_true.mpr ⟨w, hw, inB_refl w⟩)

theorem sepB_same {sz : List Nat} {i o l o' l' : Nat} (hb : i < sz.length) (h1 : o + l ≤ sz.getD i 0)
    (h2 : o' + l' ≤ sz.getD i 0) (hd : o + l ≤ o' ∨ o' + l' ≤ o) : sepB sz (i, o, l) (i, o', l') = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega_arith

/-- The polynomials the rows and `v` use: `ρ`, `t̂`, `ŷ`, `e₁`, `e₂` and `μ`. -/
structure EData (K : KemLay) (L : Lay) (b : EB) (s₀ s : State) : Prop where
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀
  v : ∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
    else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))
  e : ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N)
  mu : PolyIs s.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀))

theorem EData.keep {K : KemLay} {L : Lay} {b : EB} {s₀ s s' : State} (hL : L.Ok) (h : EData K L b s₀ s)
    {W : List (Nat × Nat × Nat)} (hf : Frame (L.RL W) s.mem s'.mem) (h1 : sepAll L.sizes (0, 1248, 32) W = true)
    (h2 : sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) W = true) : EData K L b s₀ s' := by
  have hp : ∀ k < 3 * K.k + 2, sepAll L.sizes (0, oPoly k, 1024) W = true := fun k hk =>
    sepAll_left h2 (by
      simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega_arith)
  exact ⟨(Lay.bytes_keep hL hf h1 (by decide)).trans h.rho,
    fun k hk => Lay.polyIs_keep hL hf (hp k (by omega_arith)) (h.v k hk),
    fun N h3 h7 => Lay.polyIs_keep hL hf (hp (K.k + N) (by omega_arith)) (h.e N h3 h7),
    Lay.polyIs_keep hL hf (hp (3 * K.k + 1) (by omega_arith)) h.mu⟩

/-- After the rows `i' < i`. -/
structure ERow (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] (L.RL (encW K b)) s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 i
  s4 : s.gpr .s4 = if okE K L b s₀ i then 1 else 0
  d : EData K L b s₀ s
  c : ∀ i' < i, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i')

/-- In row `i` (from `s`), with the sum `f`. -/
structure RB (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (f : Poly) (s' : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] (L.RL (rowW K)) s s'
  s6 : s'.gpr .s6 = BitVec.ofNat 64 i
  s4 : s'.gpr .s4 = if okE K L b s₀ (i + 1) then 1 else 0
  acc : PolyIs s'.mem (L.A 0 K.oAcc) f

/-- In row `i`, after its encoding. -/
structure RC (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (s' : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] (L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s'
  s6 : s'.gpr .s6 = BitVec.ofNat 64 i
  s4 : s'.gpr .s4 = if okE K L b s₀ (i + 1) then 1 else 0
  cb : bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i)) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i)

/-- How the regions of a row lie among those of `encrypt`. -/
abbrev RowFacts (K : KemLay) : Prop := (rowW K).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (rowW K).all (fun w => (encW0 K).any (inB w)) = true ∧
    (rowW K).all (sep0 1248 32) = true ∧ (rowW K).all (sep0 2048 (1024 * (3 * K.k + 2))) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (fun w => (rowW K).any (subB0 w)) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (fun w => (rowW K).any (subB0 w)) = true ∧
    (∀ i < K.k, (rowW K).all (sep0 (oPoly (K.k + (K.k + i))) 1024) = true)

theorem row_facts {K : KemLay} (hK : K.WF) : RowFacts K :=
  (by decide : ∀ k < 5, RowFacts (kOf k)) K.k (by have := hK.k4; omega_arith)

/-- A `u[i]` within `c`. -/
theorem uSlot {K : KemLay} {i : Nat} (hi : i < K.k) : K.uLen * i + K.uLen ≤ K.ctLen := by
  have : K.uLen * i + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  simp only [KemLay.ctLen]; omega_arith

/-- Two `u[i]` within `c` are apart. -/
theorem uApart {K : KemLay} {i i' : Nat} (h : i' ≠ i) :
    K.uLen * i' + K.uLen ≤ K.uLen * i ∨ K.uLen * i + K.uLen ≤ K.uLen * i' := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
  · exact .inr (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)

/-- `a0` at polynomial `j` of `scratch`, `a1` at polynomial `i` of the array from polynomial `j'`. -/
theorem ptrSlot_ok {s : State} {P : BitVec 64} {i j j' : Nat} (h11 : s.gpr .s11 = P)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hj : j + 2 < 2048) (hj' : j' + 2 < 2048) (hi : i + j' + 2 < 2 ^ 50) :
    WP isa (.block (polyAddr .a0 j ++ slotAt .a1 .s6 j')) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly j) ∧
      s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly j' + 1024 * i) := by
  rw [← List.append_nil (slotAt .a1 .s6 j')]
  exact wp_polyAddr hj (by decide) fun s₁ h₁ => wp_slotAt hj' hi (by decide)
    (by rw [h₁.other _ (by decide), h6]) fun s₂ h₂ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans (updOnly h₂ (by decide)), by rw [h₂.other _ (by decide), h₁.gpr, h11],
        by rw [h₂.gpr, h₁.other _ (by decide), h11]⟩

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

/-- The part `[k, k + n)` of `c` apart from regions inside `encW0`. -/
theorem cSep {k n : Nat} (hk : k + n ≤ K.ctLen) {W : List (Nat × Nat × Nat)}
    (hW : W.all (fun w => (encW0 K).any (inB w)) = true) : sepAll L.sizes (b.iC, b.oC + k, n) W = true :=
  sepAll_mono hp.sC (inB_off hk) hW

theorem cData {k n : Nat} (hk : k + n ≤ K.ctLen) :
    sepAll L.sizes (0, 1248, 32) [(b.iC, b.oC + k, n)] = true ∧
      sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) [(b.iC, b.oC + k, n)] = true := by
  have hK := hp.wf
  have c1 := cSep hp hk (W := [(0, 1248, 32)]) (by kdecide)
  have c2 := cSep hp hk (W := [(0, 2048, 1024 * (3 * K.k + 2))]) (by kdecide)
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at c1 c2 ⊢
  exact ⟨sepB_symm c1, sepB_symm c2⟩

theorem cBound : b.iC < L.sizes.length ∧ b.oC + K.ctLen ≤ L.size b.iC := sepAll_bounds hp.sC

theorem ERow.rowPre {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s) :
    RowPre K L (ρE K L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE K L b s₀ i) s :=
  ⟨hp.wf, h.kx.ctx (by decide) hp.ctx, hi, h.s6, h.s4, h.d.rho, fun j hj => by
    have := h.d.v (K.k + j) (by omega_arith)
    have e : ¬ (K.k + j < K.k) := by omega_arith
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega_arith] at this
    exact this⟩

section
variable {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s)
include hi h

omit hi in
theorem RB.ctx {f : Poly} {s' : State} (r : RB K L b s₀ i s f s') : Ctx L s' :=
  r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)

omit hi in
theorem er2_ok {s₁ : State}
    (r : RowInv K L true (ρE K L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE K L b s₀ i) s K.k s₁) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jNtt)) s₁ fun s₂ =>
      RB K L b s₀ i s (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀ j i) (VG.Proof.MlKem.encY (rB L s₀)) K.k) s₂ ∧
      s₂.gpr .a0 = L.A 0 K.oAcc ∧ s₂.gpr .a1 = L.A 0 K.oNtt := by
  have hK := hp.wf
  have hc₁ := r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)
  have k4 := hK.k4
  refine WP.mono (addr2_ok (by offs) (by offs) (by decide) (by decide) (by decide) hc₁.s11) fun s₂ ⟨o₂, a3, a4⟩ =>
    ⟨⟨?_, ?_, ?_, ?_⟩, a3, a4⟩
  · exact (r.kx.weaken (by simp)).trans (o₂.x _ _)
  · rw [o₂.cs .s6 (by decide), r.kx.cs .s6 (by decide) (by decide), h.s6]
  · rw [o₂.cs .s4 (by decide), r.s4, okE_succ]
  · rw [o₂.mem, ← rowAcc_eq]; exact r.acc

omit hi in
theorem er3_ok {f : Poly} {s₂ : State} (r : RB K L b s₀ i s f s₂) (g3 : s₂.gpr .a0 = L.A 0 K.oAcc)
    (g4 : s₂.gpr .a1 = L.A 0 K.oNtt) : WP isa callNttInv s₂ (RB K L b s₀ i s (nttInv f)) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, c5, -, -⟩ := row_facts hK
  exact nttInvL hp.ctx.ok g3 g4 (hc.sep00 (by offs) (by offs) (by offs)) hc.cw hc.cw r.acc (hc.alP _) (hc.alP _)
    fun s₃ k₃ p₃ => ⟨r.kx.trans ((k₃.x _).subL hp.ctx c5), by rw [k₃.cs .s6 (by decide), r.s6],
      by rw [k₃.cs .s4 (by decide), r.s4], p₃⟩

theorem er4_ok {f : Poly} {s₃ : State} (r : RB K L b s₀ i s f s₃) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ slotAt .a1 .s6 (2 * K.k))) s₃ fun s₄ =>
      RB K L b s₀ i s f s₄ ∧ s₄.gpr .a0 = L.A 0 K.oAcc ∧ s₄.gpr .a1 = L.A 0 (oPoly (K.k + (K.k + i))) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hc := r.ctx hp h
  refine WP.mono (ptrSlot_ok (i := i) hc.s11 r.s6 (by offs) (by offs) (by offs)) fun s₄ ⟨o₄, a3, a4⟩ => ?_
  rw [show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a4
  exact ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .s6 (by decide), r.s6],
    by rw [o₄.cs .s4 (by decide), r.s4], by rw [o₄.mem]; exact r.acc⟩, a3, a4⟩

theorem er5_ok {f : Poly} {s₄ : State} (r : RB K L b s₀ i s f s₄) (g3 : s₄.gpr .a0 = L.A 0 K.oAcc)
    (g4 : s₄.gpr .a1 = L.A 0 (oPoly (K.k + (K.k + i)))) :
    WP isa callAdd s₄ (RB K L b s₀ i s (add f (VG.Proof.MlKem.cbd (rB L s₀) (K.k + i)))) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, -, c6, c7⟩ := row_facts hK
  have he : PolyIs s₄.mem (L.A 0 (oPoly (K.k + (K.k + i)))) (VG.Proof.MlKem.cbd (rB L s₀) (K.k + i)) :=
    Lay.polyIs_keep hp.ctx.ok r.kx.frame (hc.sepAll0 (by offs) (c7 i hi)) (h.d.e (K.k + i) (by omega_arith) (by omega_arith))
  exact addL hp.ctx.ok g3 g4 (hc.sep00 (by offs) (by offs) (by offs)) hc.cw (mem_rd_wr hc.cw) r.acc he
    (hc.alP _) (hc.alP _) fun s₅ k₅ p₅ => ⟨r.kx.trans ((k₅.x _).subL hp.ctx c6), by rw [k₅.cs .s6 (by decide), r.s6],
      by rw [k₅.cs .s4 (by decide), r.s4], p₅⟩

omit hp hi h in
theorem cArgs_ok (hK : K.WF) {s : State} {P C : BitVec 64} {i : Nat} (h11 : s.gpr .s11 = P)
    (h7 : s.gpr .s7 = C) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) :
    WP isa (.block (atMul .a2 .s7 .s6 K.uLen ++ polyAddr .a0 K.jAcc ++ ([.li .a1 K.du, .li .a3 K.uLen] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 K.oAcc ∧ s'.gpr .a1 = BitVec.ofNat 64 K.du ∧
        s'.gpr .a2 = C + BitVec.ofNat 64 (K.uLen * i) ∧ s'.gpr .a3 = BitVec.ofNat 64 (32 * K.du) := by
  have k4 := hK.k4
  have e2 : K.du < 2048 := by offs
  have e3 : K.uLen < 2048 := by offs
  simp only [List.append_assoc]
  refine wp_atMul e3 (by decide) (by decide) fun s₁ u₁ => wp_polyAddr (by offs) (by decide) fun s₂ h₂ =>
    wp_li e2 fun s₃ h₃ => wp_li e3 fun s₄ h₄ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n0, n1, n2, n3, n4, -⟩ := pres_ne hr
    rw [h₄.other _ n4, h₃.other _ n2, h₂.other _ n1, u₁.other _ n3 n0]
  · rw [h₄.mem, h₃.mem, h₂.mem, u₁.mem]
  · rw [h₄.rd, h₃.rd, h₂.rd, u₁.rd]
  · rw [h₄.wr, h₃.wr, h₂.wr, u₁.wr]
  · rw [h₄.sp, h₃.sp, h₂.sp, u₁.sp]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide) (by decide), h11]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), u₁.gpr, h7, h6, mul_eq]
  · rw [h₄.gpr]

omit hi in
theorem er6_ok {f : Poly} {s₅ : State} (r : RB K L b s₀ i s f s₅) :
    WP isa (.block (atMul .a2 .s7 .s6 K.uLen ++ polyAddr .a0 K.jAcc ++ ([.li .a1 K.du, .li .a3 K.uLen] : List Instr))) s₅
      fun s₆ => RB K L b s₀ i s f s₆ ∧ s₆.gpr .a0 = L.A 0 K.oAcc ∧
        s₆.gpr .a1 = BitVec.ofNat 64 K.du ∧ s₆.gpr .a2 = L.A b.iC (b.oC + K.uLen * i) ∧
        s₆.gpr .a3 = BitVec.ofNat 64 (32 * K.du) := by
  have hc := r.ctx hp h
  have g27 : s₅.gpr .s7 = L.A b.iC b.oC := by
    rw [r.kx.cs .s7 (by decide) (by decide), h.kx.cs .s7 (by decide) (by decide), hp.s7]
  refine WP.mono (cArgs_ok hp.wf hc.s11 g27 r.s6) fun s₆ ⟨o₆, a3, a4, a5, a6⟩ => ?_
  rw [ptr_add] at a5
  exact ⟨⟨r.kx.trans (o₆.x _ _), by rw [o₆.cs .s6 (by decide), r.s6],
    by rw [o₆.cs .s4 (by decide), r.s4], by rw [o₆.mem]; exact r.acc⟩, a3, a4, a5, a6⟩

theorem er7_ok {s₆ : State} (r : RB K L b s₀ i s (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i) s₆)
    (g3 : s₆.gpr .a0 = L.A 0 K.oAcc) (g4 : s₆.gpr .a1 = BitVec.ofNat 64 K.du)
    (g5 : s₆.gpr .a2 = L.A b.iC (b.oC + K.uLen * i)) (g6 : s₆.gpr .a3 = BitVec.ofNat 64 (32 * K.du)) :
    WP isa K.callCU s₆ (RC K L b s₀ i s) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  have hs : sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * i, 32 * K.du) = true := by
    have := cSep hp (k := K.uLen * i) (n := K.uLen) (uSlot hi) (W := [(0, K.oAcc, 1024)]) (by kdecide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  exact hp.calls.cu hp.ctx.ok g3 g4 g5 g6 (.inl rfl) hs (mem_rd_wr hc.cw)
    (by rw [r.kx.wr, h.kx.wr]; exact hp.wC) r.acc (hc.alP _) fun s₇ k₇ p₇ =>
    ⟨(r.kx.monoL (by simp)).trans ((k₇.x _).monoL (by simp)), by rw [k₇.cs .s6 (by decide), r.s6],
      by rw [k₇.cs .s4 (by decide), r.s4], p₇⟩

theorem er8_ok {s₇ : State} (r : RC K L b s₀ i s s₇) :
    WP isa (.block (count .s6 K.k)) s₇ fun s' =>
      ERow K L b s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨r1, r2, r3, r4, -, -, -⟩ := row_facts hK
  obtain ⟨cb1, cb2⟩ := cBound hp
  refine WP.mono (count_ok (by decide) (by omega_arith) (by omega_arith) r.s6) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.s6, .s5, .s4] (L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · refine h.kx.trans ?_
    have e : ∀ w ∈ L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)]),
        ∃ w' ∈ L.RL (encW K b), Region.Sub w w' := by
      intro w hw
      simp only [Lay.RL, List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨w', hw', hs⟩ := hp.ctx.subL r1 w hw
        exact ⟨w', by simp only [Lay.RL, List.map_append, List.mem_append]; exact .inl hw', hs⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
        have := uSlot (K := K) hi
        exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R L (by omega_arith) (by omega_arith)⟩
    exact K'.sub e
  · rw [k'.cs .s4 (by decide) (by decide), r.s4]
  · obtain ⟨d1, d2⟩ := cData hp (k := K.uLen * i) (n := K.uLen) (uSlot hi)
    exact h.d.keep hL K'.frame (sepAll_append (hp.ctx.sepAll0 (by decide) r3) d1)
      (sepAll_append (hp.ctx.sepAll0 (by offs) r4) d2)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by offs)).trans r.cb
    · have u1 := uSlot (K := K) (i := i') (by omega_arith)
      have u2 := uSlot (K := K) hi
      have s1 : sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) (rowW K) = true := cSep hp (by omega_arith) r2
      have s2 : sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) [(b.iC, b.oC + K.uLen * i, K.uLen)] = true := by
        simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
        exact sepB_same cb1 (by simp only [Lay.size] at cb2; omega_arith) (by simp only [Lay.size] at cb2; omega_arith)
          (by have := uApart (K := K) e; omega_arith)
      rw [← h.c i' (by omega_arith)]
      exact Lay.bytes_keep hL K'.frame (sepAll_append s1 s2) (by offs)

end

theorem encRow_step {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s) :
    WP isa K.encRowBody s fun s' => ERow K L b s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) :=
  WP.seq (WP.mono (rowSum_ok (transpose := true) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (er2_ok hp h r₁) fun _ ⟨r₂, a3, a4⟩ =>
    WP.seq (WP.mono (er3_ok hp h r₂ a3 a4) fun _ r₃ =>
    WP.seq (WP.mono (er4_ok hp hi h r₃) fun _ ⟨r₄, b3, b4⟩ =>
    WP.seq (WP.mono (er5_ok hp hi h r₄ b3 b4) fun _ r₅ =>
    WP.seq (WP.mono (er6_ok hp h r₅) fun _ ⟨r₆, c3, c4, c5, c6⟩ =>
    WP.seq (WP.mono (er7_ok hp hi h r₆ c3 c4 c5 c6) fun _ r₇ => er8_ok hp hi h r₇)))))))

end

/-! ## `v` -/

/-- What the steps of `v` keep: what the rows left. -/
structure VEnv (K : KemLay) (L : Lay) (b : EB) (s₀ s : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] (L.RL (encW K b)) s₀ s
  s4 : s.gpr .s4 = if okE K L b s₀ K.k then 1 else 0
  d : EData K L b s₀ s
  c : ∀ i' < K.k, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i')

/-- A region of `scratch` the steps of `v` may change. -/
def vOK (K : KemLay) (w : Nat × Nat × Nat) : Bool :=
  (encW0 K).any (subB0 w) && (encW0 K).any (inB w) && sep0 1248 32 w && sep0 2048 (1024 * (3 * K.k + 2)) w

/-- What `v` writes keeps `VEnv`. -/
abbrev VOKFacts (K : KemLay) : Prop := (dotW K).all (vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (vOK K) = true

theorem vOK_facts {K : KemLay} (hK : K.WF) : VOKFacts K :=
  (by decide : ∀ k < 5, VOKFacts (kOf k)) K.k (by have := hK.k4; omega_arith)

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem VEnv.keep {s s' : State} (h : VEnv K L b s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (k : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.s6, .s5]) (hW : W.all (vOK K) = true) :
    VEnv K L b s₀ s' := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  have w1 : W.all (fun w => (encW0 K).any (subB0 w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.1
  have w2 : W.all (fun w => (encW0 K).any (inB w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.2
  have w3 : W.all (sep0 1248 32) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.2
  have w4 : W.all (sep0 2048 (1024 * (3 * K.k + 2))) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.kx.trans ?_, ?_, h.d.keep hL k.frame (hc.sepAll0 (by decide) w3) (hc.sepAll0 (by offs) w4),
    fun i' hi' => (Lay.bytes_keep hL k.frame (cSep hp (uSlot hi') w2)
      (by simp only [KemLay.uLen]; have := hK.du; omega_arith)).trans (h.c i' hi')⟩
  · refine ((k.weaken fun x hx' => ?_).subL hp.ctx w1).monoL fun w hw => List.mem_append_left _ hw
    have := hx x hx'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl <;> simp
  · rw [k.cs .s4 (by decide) (fun hm => by have := hx _ hm; simp at this), h.s4]

omit hp in
theorem ERow.venv {s : State} (h : ERow K L b s₀ K.k s) : VEnv K L b s₀ s := ⟨h.kx, h.s4, h.d, h.c⟩

theorem ev1_ok {s : State} (h : VEnv K L b s₀ s) :
    WP isa K.dot s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀)) (VG.Proof.MlKem.encY (rB L s₀)) K.k) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  refine WP.mono (dot_ok hK hc (fun j hj => ?_) (fun j hj => ?_)) fun s' ⟨k, p⟩ =>
    ⟨h.keep hp k (by simp) (vOK_facts hK).1, p⟩
  · have := h.d.v j (by omega_arith); simp only [hj, ↓reduceIte] at this; exact this
  · have := h.d.v (K.k + j) (by omega_arith)
    have e : ¬ (K.k + j < K.k) := by omega_arith
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega_arith] at this
    exact this

theorem evArgs_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s) (hf : PolyIs s.mem (L.A 0 K.oAcc) f) {j : Nat}
    (hj : j + 2 < 2048) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 j)) s fun s' =>
      (VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧
      s'.gpr .a0 = L.A 0 K.oAcc ∧ s'.gpr .a1 = L.A 0 (oPoly j) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hc := h.kx.ctx (by decide) hp.ctx
  exact WP.mono (addr2_ok (by offs) hj (by decide) (by decide) (by decide) hc.s11) fun s' ⟨o', a3, a4⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl,
      by rw [o'.mem]; exact hf⟩, a3, a4⟩

theorem ev3_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f)
    (g3 : s.gpr .a0 = L.A 0 K.oAcc) (g4 : s.gpr .a1 = L.A 0 K.oNtt) :
    WP isa callNttInv s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (nttInv f) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact nttInvL hp.ctx.ok g3 g4 (hc.sep00 (by offs) (by offs) (by offs)) hc.cw hc.cw h.2 (hc.alP _) (hc.alP _)
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (vOK_facts hK).2.1, p⟩

theorem evAdd_ok {s : State} {f g : Poly} {k : Nat} (hk : k = 3 * K.k ∨ k = 3 * K.k + 1)
    (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) (hg : PolyIs s.mem (L.A 0 (oPoly k)) g)
    (g3 : s.gpr .a0 = L.A 0 K.oAcc) (g4 : s.gpr .a1 = L.A 0 (oPoly k)) :
    WP isa callAdd s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (add f g) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact addL hp.ctx.ok g3 g4 (hc.sep00 (by offs) (by rcases hk with rfl | rfl <;> offs)
    (by rcases hk with rfl | rfl <;> offs)) hc.cw (mem_rd_wr hc.cw) h.2 hg (hc.alP _) (hc.alP _)
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (vOK_facts hK).2.2, p⟩

omit hp in
theorem vArgs_ok (hK : K.WF) {s : State} {P C : BitVec 64} (h11 : s.gpr .s11 = P) (h7 : s.gpr .s7 = C) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ ([.li .a1 K.dv, .addi .a2 .s7 (K.uLen * K.k), .li .a3 K.vLen] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 K.oAcc ∧ s'.gpr .a1 = BitVec.ofNat 64 K.dv ∧
        s'.gpr .a2 = C + BitVec.ofNat 64 (K.uLen * K.k) ∧ s'.gpr .a3 = BitVec.ofNat 64 (32 * K.dv) := by
  have k4 := hK.k4
  have e2 : K.dv < 2048 := by offs
  have e3 : K.uLen * K.k < 2048 := by
    have := hK.du
    simp only [KemLay.uLen]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul_left 32 this) k4) (by decide)
  have e4 : K.vLen < 2048 := by offs
  refine wp_polyAddr (by offs) (by decide) fun s₁ h₁ => wp_li e2 fun s₂ h₂ => wp_addi e3 fun s₃ h₃ =>
    wp_li e4 fun s₄ h₄ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
        (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h11]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), h7]
  · rw [h₄.gpr]

theorem ev8_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ ([.li .a1 K.dv, .addi .a2 .s7 (K.uLen * K.k), .li .a3 K.vLen] : List Instr))) s
      fun s' => (VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧ s'.gpr .a0 = L.A 0 K.oAcc ∧
        s'.gpr .a1 = BitVec.ofNat 64 K.dv ∧ s'.gpr .a2 = L.A b.iC (b.oC + K.uLen * K.k) ∧
        s'.gpr .a3 = BitVec.ofNat 64 (32 * K.dv) := by
  have hc := h.1.kx.ctx (by decide) hp.ctx
  have g27 : s.gpr .s7 = L.A b.iC b.oC := by
    rw [h.1.kx.cs .s7 (by decide) (by decide), hp.s7]
  exact WP.mono (vArgs_ok hp.wf hc.s11 g27) fun s' ⟨o', a3, a4, a5, a6⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl,
      by rw [o'.mem]; exact h.2⟩, a3, a4, by rw [a5, ptr_add], a6⟩

omit hp in
/-- `c * k` bytes as `k` pieces of `c`. -/
theorem bytes_catK (m : Mem) (p : Addr) (c : Nat) :
    ∀ k, bytesAt m p (c * k) = VG.Proof.MlKem.KPke.catK (fun i => bytesAt m (p + BitVec.ofNat 64 (c * i)) c) k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, bytesAt_add, bytes_catK m p c k]
    exact (VG.Proof.MlKem.KPke.foldK_succ List.nil_append _ k).symm

omit hp in
theorem catK_congr {f g : Nat → List Byte} : ∀ {k}, (∀ i < k, f i = g i) →
    VG.Proof.MlKem.KPke.catK f k = VG.Proof.MlKem.KPke.catK g k
  | 0, _ => rfl
  | k + 1, h => by
    show VG.Proof.MlKem.KPke.foldK (· ++ ·) [] f (k + 1) = VG.Proof.MlKem.KPke.foldK (· ++ ·) [] g (k + 1)
    rw [VG.Proof.MlKem.KPke.foldK_succ List.nil_append, VG.Proof.MlKem.KPke.foldK_succ List.nil_append,
      h k (by omega_arith)]
    exact congrArg (· ++ g k) (catK_congr fun i hi => h i (by omega_arith))

theorem ev9_ok {s : State} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀) (mB L b s₀) (rB L s₀)))
    (g3 : s.gpr .a0 = L.A 0 K.oAcc) (g4 : s.gpr .a1 = BitVec.ofNat 64 K.dv)
    (g5 : s.gpr .a2 = L.A b.iC (b.oC + K.uLen * K.k)) (g6 : s.gpr .a3 = BitVec.ofNat 64 (32 * K.dv)) :
    WP isa K.callCU s fun s' => KeptX [.s6, .s5, .s4] (L.RL (encW K b)) s₀ s' ∧
      s'.gpr .s4 = (if okE K L b s₀ K.k then 1 else 0) ∧
      bytesAt s'.mem (L.A b.iC b.oC) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (aE K L b s₀) (ekB K L b s₀) (mB L b s₀) (rB L s₀) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  obtain ⟨cb1, cb2⟩ := cBound hp
  have hs : sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * K.k, 32 * K.dv) = true := by
    have := cSep hp (k := K.uLen * K.k) (n := K.vLen) (by simp only [KemLay.ctLen]; omega_arith)
      (W := [(0, K.oAcc, 1024)]) (by kdecide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  have ect : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl
  have du := hK.du
  simp only [Lay.size] at cb2
  refine hp.calls.cu hL g3 g4 g5 g6 (.inr rfl) hs (mem_rd_wr hc.cw)
    (by rw [h.1.kx.wr]; exact hp.wC) h.2 (hc.alP _) fun s' k p => ⟨?_, ?_, ?_⟩
  · refine h.1.kx.trans ((k.x _).sub fun r hr => ?_)
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R L (by omega_arith) (by omega_arith)⟩
  · rw [k.cs .s4 (by decide), h.1.s4]
  · have keep : ∀ i' < K.k, bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
        compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i') := fun i' hi' => by
      have u1 := uSlot (K := K) hi'
      have u2 : K.uLen * i' + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'
      rw [← h.1.c i' hi']
      refine Lay.bytes_keep hL k.frame ?_ (by simp only [KemLay.uLen]; omega_arith)
      simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
      exact sepB_same cb1 (by omega_arith) (by omega_arith) (by omega_arith)
    simp only [Lay.A] at keep p ⊢
    rw [KemLay.ctLen, bytesAt_add, bytes_catK, ptr_add, VG.Proof.MlKem.KPke.ct, ← p]
    congr 1
    refine catK_congr fun i hi => ?_
    rw [ptr_add]; exact keep i hi

end

/-! ## The whole of K-PKE.Encrypt -/

/-- `μ` apart from the polynomials of the `PRF`s. -/
abbrev MuSep (K : KemLay) : Prop :=
  (∀ k < 2 * K.k, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (sep0 (oPoly k) 1024) = true) ∧
    (∀ N < 2 * K.k + 1, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (sep0 (oPoly (K.k + N)) 1024) = true)

theorem mu_sep {K : KemLay} (hK : K.WF) : MuSep K :=
  (by decide : ∀ k < 5, MuSep (kOf k)) K.k (by have := hK.k4; omega_arith)

theorem flagInit_ok {s : State} :
    WP isa (.block [.li .s4 1, .li .s6 0]) s fun s' =>
      KeptX [.s6, .s4] [] s s' ∧ s'.gpr .s4 = 1 ∧ s'.gpr .s6 = 0 ∧ s'.mem = s.mem :=
  wp_li (by decide) fun s₁ h₁ => wp_li (by decide) fun s₂ h₂ => WP.block_nil
    ⟨⟨fun r _ hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [h₂.other _ hx.1, h₁.other _ hx.2], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
        by rw [h₂.mem, h₁.mem]; exact Frame.refl _ _⟩,
      by rw [h₂.other _ (by decide), h₁.gpr]; rfl, by rw [h₂.gpr]; rfl, by rw [h₂.mem, h₁.mem]⟩

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem dec_pre {s₁ : State} (e₁ : EA K L s₀ s₁) :
    Ctx L s₁ ∧ s₁.gpr .s10 = L.A b.iE b.oE ∧
      sepAll L.sizes (b.iE, b.oE, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧ L.buf b.iE ∈ s₁.rd ++ s₁.wr := by
  have hK := hp.wf
  exact ⟨EA.ctx hp e₁, by rw [EA.reg e₁ (by simp), hp.s10], sepAll_mono hp.sE (by simp [inB]) (by kdecide),
    by rw [e₁.rd, e₁.wr]; exact hp.wE⟩

omit hp in
theorem v_of {s₃ : State} (t₃ : ∀ k < K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k))
    (y₃ : ∀ j < K.k, PolyIs s₃.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j)) :
    ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k)) := fun k hk => by
  by_cases e : k < K.k
  · simp only [e, ↓reduceIte]; exact t₃ k e
  · simp only [e, ↓reduceIte]
    have := y₃ (k - K.k) (by omega_arith)
    rwa [show K.k + (k - K.k) = k by omega_arith] at this

theorem rows_init {s₅ : State} (e₅ : EA K L s₀ s₅) (d₅ : EData K L b s₀ s₅) :
    WP isa (.block [.li .s4 1, .li .s6 0]) s₅ (ERow K L b s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k, g24, g26, m⟩ =>
    ⟨(e₅.monoL fun w hw => List.mem_append_left _ hw).trans ((k.weaken (by simp)).mono
      (fun _ h => absurd h List.not_mem_nil)), g26, by rw [g24]; rfl,
      d₅.keep hp.ctx.ok (W := []) (by rw [m]; exact Frame.refl _ _) rfl rfl,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem data5 {s₄ s₅ : State} (ρ₄ : bytesAt s₄.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (v₄ : ∀ k < 2 * K.k, PolyIs s₄.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k)))
    (E₄ : ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
      PolyIs s₄.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N))
    (f₅ : Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s₅.mem)
    (μ₅ : PolyIs s₅.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀))) : EData K L b s₀ s₅ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  exact ⟨(Lay.bytes_keep hL f₅ (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans ρ₄,
    fun k hk => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((mu_sep hK).1 k hk)) (v₄ k hk),
    fun N h3 h7 => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((mu_sep hK).2 N h7)) (E₄ N h3 h7), μ₅⟩

theorem encrypt_ok : WP isa K.encrypt s₀ fun s => KeptX [.s6, .s5, .s4] (L.RL (encW K b)) s₀ s ∧
    s.gpr .s4 = (if okE K L b s₀ K.k then 1 else 0) ∧
    bytesAt s.mem (L.A b.iC b.oC) K.ctLen =
      VG.Proof.MlKem.KPke.ct K.p (aE K L b s₀) (ekB K L b s₀) (mB L b s₀) (rB L s₀) := by
  have hK := hp.wf
  refine WP.seq (WP.mono (enc1_ok hp) fun s₁ ⟨e₁, _, ρ₁⟩ => ?_)
  obtain ⟨hc₁, g30, hsE, hr₁⟩ := dec_pre hp e₁
  refine WP.seq (WP.mono (decT_init (K := K) (L := L) (i := b.iE) (o := b.oE)) fun s₁' h₁' => ?_)
  refine WP.seq (WP.mono (decT_loop hK hc₁ g30 hsE hr₁ h₁') fun s₂ h₂ => ?_)
  obtain ⟨e₂, ρ₂, t₂⟩ := enc2_ok hp e₁ ρ₁ h₂
  refine WP.seq (WP.mono (enc3_ok hp e₂ ρ₂ t₂) fun s₃ ⟨e₃, ρ₃, t₃, y₃⟩ => ?_)
  refine WP.seq (WP.mono (enc4_ok hp e₃ ρ₃ (v_of t₃ y₃)) fun s₄ ⟨e₄, ρ₄, v₄, E₄⟩ => ?_)
  refine WP.seq (WP.mono (enc5a_ok hp e₄) fun s₄' ⟨h₄', a3, a4, a5, a6⟩ => ?_)
  refine WP.seq (WP.mono (enc5b_ok hp e₄ h₄' a3 a4 a5 a6) fun s₅ ⟨e₅, f₅, μ₅⟩ => ?_)
  have d₅ := data5 hp ρ₄ v₄ E₄ f₅ μ₅
  refine WP.seq (WP.mono (rows_init hp e₅ d₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (ERow K L b s₀) (N := K.k) (by have := hK.k1; omega_arith)
    (fun i hi s h => encRow_step hp hi h) (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (ev1_ok hp h₇.venv) fun s₈ h₈ => ?_)
  have k4 := hK.k4
  refine WP.seq (WP.mono (evArgs_ok hp h₈.1 h₈.2 (j := K.jNtt) (by offs)) fun s₉ ⟨h₉, a3, a4⟩ => ?_)
  refine WP.seq (WP.mono (ev3_ok hp h₉ a3 a4) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₀.1 h₁₀.2 (j := 3 * K.k) (by offs)) fun s₁₁ ⟨h₁₁, b3, b4⟩ => ?_)
  have e₁₁ := h₁₁.1.d.e (2 * K.k) (by omega_arith) (by omega_arith)
  rw [show K.k + 2 * K.k = 3 * K.k by omega_arith] at e₁₁
  refine WP.seq (WP.mono (evAdd_ok hp (.inl rfl) h₁₁ e₁₁ b3 b4) fun s₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₂.1 h₁₂.2 (j := 3 * K.k + 1) (by offs))
    fun s₁₃ ⟨h₁₃, c3, c4⟩ => ?_)
  refine WP.seq (WP.mono (evAdd_ok hp (.inr rfl) h₁₃ h₁₃.1.d.mu c3 c4) fun s₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (ev8_ok hp h₁₄) fun s₁₅ ⟨h₁₅, d3, d4, d5, d6⟩ => ?_)
  exact ev9_ok hp h₁₅ d3 d4 d5 d6

end

/-! ## The matrix, for the contracts -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem enc_some {k : Nat} {ρ r : List Byte} (hk : okEnc k ρ k = true) :
    ∀ i < k, ∀ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = some (aEnc ρ r i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
  have h₂ := List.all_eq_true.mp h₁ i (List.mem_range.mpr hi)
  simp only [rowSeed, ↓reduceIte] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aEnc, effA, rowSeed, ↓reduceIte, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem enc_none {k : Nat} {ρ : List Byte} (hk : okEnc k ρ k = false) :
    ∃ i < k, ∃ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = none := by
  rw [okEnc, List.all_eq_false] at hk
  obtain ⟨j, hj, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨i, hi, h₂⟩ := h₁
  simp only [rowSeed, ↓reduceIte] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

end Enc

end VG.Proof.MlKem.RISCV64
