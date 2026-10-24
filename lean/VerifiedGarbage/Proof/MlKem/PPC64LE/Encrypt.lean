module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: K-PKE.Encrypt, correctness

As on 32-bit ARM (`Proof/MlKem/Arm/Encrypt.lean`). `K.encrypt` runs within
encapsulation and decapsulation, on buffers the callers choose (`EB`): the
encapsulation key (in `r30`), the message (in `r29`) and the ciphertext (in
`r27`), each at an offset of one of the callers' buffers; `r` is at 952 in
`scratch`. It writes the ciphertext, and changes nothing but the regions of
`encW` (`encrypt_ok`). Its phases: `ρ` copied to the seed of `SampleNTT`,
`t̂` decoded (`decT_loop`), the `PRF`s into `ŷ`, `e₁` and `e₂`, `μ`, the rows
of `u` compressed into the ciphertext (`encRow_step`), and `v`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

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
  omega

theorem sepAll_mono {sz : List Nat} {a a' : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W' = true) (ha : inB a' a = true) (hW : W.all (fun w => W'.any (inB w)) = true) :
    sepAll sz a' W = true :=
  List.all_eq_true.mpr fun w hw => by
    obtain ⟨w', hw', hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hW w hw)
    exact sepB_mono (List.all_eq_true.mp h w' hw') ha hi

theorem inB_off {i o l k n : Nat} (h : k + n ≤ l) : inB (i, o + k, n) (i, o, l) = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem inB_refl (w : Nat × Nat × Nat) : inB w w = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- The bounds of a region apart from another. -/
theorem sepAll_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz (i, o, l) (w :: W) = true) : i < sz.length ∧ o + l ≤ sz.getD i 0 :=
  sepB_bounds (List.all_eq_true.mp h w (List.mem_cons_self ..))

/-! ## Copying from an offset -/

theorem copyLo {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {bo so dO len i j : Nat}
    (hsb : sb ∈ preserved) (hdb : db ∈ preserved) (gs : s.gpr sb = L.A i bo) (gd : s.gpr db = L.ptr j)
    (hse : so < 32768) (hde : dO < 32768) (hle : len < 32768) (hl0 : 0 < len)
    (hs : sepB L.sizes (i, bo + so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i (bo + so)) len := by
  refine WP.seq (WP.mono (copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g3, g4, g5⟩ => ?_)
  rw [gs, ptr_add] at g3; rw [gd] at g4
  refine WP.mono (copy_loop (by omega) hl0 (Lay.disj hL hs)
    (by rw [o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g3 g4 g5)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨(o₁.kept _).trans ⟨cs, sp, rd, wr, fr⟩, ?_⟩
  rw [o₁.mem] at hb; exact hb

/-! ## Products with constants -/

theorem mul_eq (p : BitVec 64) (m i : Nat) : p + BitVec.ofNat 64 i * BitVec.ofNat 64 m = p + BitVec.ofNat 64 (m * i) := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- `d ← b + m c`, through `r0`. -/
theorem atMul_ok {s : State} {d b c : Reg} {m : Nat} (hb : b ≠ .r0) (hc : c ≠ .r0)
    (hm : m < 32768) :
    WP isa (.block (atMul d b c m)) s fun s' =>
      s'.gpr d = s.gpr b + s.gpr c * BitVec.ofNat 64 m ∧ (∀ r, r ≠ d → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  prun [atMul, exec_mul, hm, hb, hc, Ne.symm hb, Ne.symm hc]
  refine ⟨trivial, fun r h1 h2 => ?_, trivial⟩
  rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h2]

/-! ## Decoding `t̂` -/

theorem decTArgs_ok {s : State} {P B : BitVec 64} {i : Nat} (h31 : s.gpr .r31 = P) (h30 : s.gpr .r30 = B)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 i) :
    WP isa (.block (atMul .r3 .r30 .r26 384 ++ slotAt .r4 .r26 (oPoly 0))) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = B + BitVec.ofNat 64 (384 * i) ∧
      s'.gpr .r4 = P + BitVec.ofNat 64 i <<< 10 + BitVec.ofNat 64 (oPoly 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (atMul_ok (d := .r3) (by decide) (by decide) (by decide)) fun s₁ ⟨e3, o₁, m₁, rd₁, wr₁,
    sp₁⟩ => ?_
  have g31 : s₁.gpr .r31 = P := by rw [o₁ .r31 (by decide) (by decide), h31]
  have g26 : s₁.gpr .r26 = BitVec.ofNat 64 i := by rw [o₁ .r26 (by decide) (by decide), h26]
  have e1 : oPoly 0 < 32768 := by decide
  prun [slotAt, e1, g31, g26]
  refine ⟨⟨fun r hr => ?_, m₁, rd₁, wr₁, sp₁⟩, by rw [e3, h30, h26, mul_eq], trivial⟩
  have := pres_ne hr
  rw [RegUpd.gpr_write_of_ne _ _ (by intro e; subst e; simp at this), RegUpd.gpr_write_of_ne _ _
    (by intro e; subst e; simp at this), RegUpd.gpr_write_of_ne _ _ (by intro e; subst e; simp at this),
    o₁ r (fun e => this.2.1 e) this.1]

/-- The polynomials `0` to `k - 1` decoded from the `384 k` bytes at offset `o` of buffer `i` (in `r30`). -/
structure DecInv (K : KemLay) (L : Lay) (i o : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r26] (L.RL [(0, 2048, 1024 * K.k)]) s₀ s
  r26 : s.gpr .r26 = BitVec.ofNat 64 j
  t : ∀ k < j, PolyIs s.mem (L.A 0 (oPoly k)) (decode12 (bytesAt s₀.mem (L.A i (o + 384 * k)) 384))

/-- Polynomial `k < K.k` of `t̂` is in what the decoding writes, apart from the others. -/
abbrev DecTSlots (K : KemLay) : Prop :=
  ∀ k < K.k, [((0 : Nat), oPoly k, (1024 : Nat))].all (fun w => [(0, 2048, 1024 * K.k)].any (subB0 w)) = true ∧
    (∀ k' < K.k, k' ≠ k → [((0 : Nat), oPoly k, (1024 : Nat))].all (sep0 (oPoly k') 1024) = true)

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem decT_slots : DecTSlots K := (by decide : ∀ k < 5, DecTSlots (kOf k)) K.k (by have := hK.k4; omega)

theorem decT_step {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h30 : s₀.gpr .r30 = L.A i o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr)
    {j : Nat} (hj : j < K.k) {s : State} (h : DecInv K L i o s₀ j s) :
    WP isa K.decTBody s fun s' => DecInv K L i o s₀ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hc' := h.kx.ctx (by decide) hc
  obtain ⟨c_sub, c_sep⟩ := decT_slots hK j hj
  have g30 : s.gpr .r30 = L.A i o := by rw [h.kx.cs .r30 (by decide) (by decide), h30]
  refine WP.seq (WP.mono (decTArgs_ok hc'.r31 g30 h.r26) fun s₁ ⟨o₁, a3, a4⟩ => ?_)
  rw [ptr_add] at a3
  rw [slot_eq _ (by offs), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega] at a4
  have hc₁ := hc'.only o₁
  have hsj : sepAll L.sizes (i, o + 384 * j, 384) [(0, 2048, 1024 * K.k)] = true :=
    sepAll_mono hs (inB_off (by omega)) (by kdecide)
  have hsep : sepB L.sizes (i, o + 384 * j, 384) (0, oPoly j, 1024) = true :=
    sepB_mono (List.all_eq_true.mp hsj _ (List.mem_singleton_self _)) (inB_refl _) (by
      simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  refine WP.seq (decode12L hL a3 a4 hsep (by rw [o₁.rd, o₁.wr, h.kx.rd, h.kx.wr]; exact hr) hc₁.cw
    fun s₂ k₂ p₂ => ?_)
  have g26 : s₂.gpr .r26 = BitVec.ofNat 64 j := by
    rw [k₂.cs .r26 (by decide), o₁.cs .r26 (by decide), h.r26]
  refine WP.mono (count_ok (by decide) (by omega) (by omega) g26) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
  all_goals have K : KeptX [.r26] (L.RL [(0, oPoly j, 1024)]) s s' :=
    (o₁.x _ _).trans ((k₂.x _).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))
  · exact h.kx.trans (K.subL hc c_sub)
  · intro k hk
    have hb : bytesAt s.mem (L.A i (o + 384 * j)) 384 = bytesAt s₀.mem (L.A i (o + 384 * j)) 384 :=
      Lay.bytes_keep hL h.kx.frame hsj (by decide)
    by_cases e : k = j
    · subst e
      rw [o₁.mem, hb] at p₂
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₂
    · exact Lay.polyIs_keep hL K.frame (hc.sepAll0 (by offs) (c_sep k (by omega) e)) (h.t k (by omega))

omit hK in
theorem decT_init {L : Lay} {i o : Nat} {s₀ : State} :
    WP isa (.block [.li .r26 0]) s₀ (DecInv K L i o s₀ 0) :=
  WP.mono (li_ok .r26 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem decT_loop {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h30 : s₀.gpr .r30 = L.A i o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr) {s : State}
    (h : DecInv K L i o s₀ 0 s) : WP isa (.loop K.decTBody (.nonzero .d .r0)) s (DecInv K L i o s₀ K.k) :=
  wp_loop_nz (DecInv K L i o s₀) (N := K.k) (by have := hK.k1; omega)
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
  [(0, 0, 840), (0, 984, 1), (0, 1056, 128), (0, 1248, 34), (0, 2048, 1024 * (3 * K.k + 5)), (0, K.oSample, 3072),
    (1, 0, 48)]

/-- What `encrypt` changes. -/
abbrev encW (K : KemLay) (b : EB) : List (Nat × Nat × Nat) := encW0 K ++ [(b.iC, b.oC, K.ctLen)]

/-- A state `encrypt` runs from. -/
structure EncPre (K : KemLay) (L : Lay) (b : EB) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  ctx : Ctx L s
  r30 : s.gpr .r30 = L.A b.iE b.oE
  r29 : s.gpr .r29 = L.A b.iM b.oM
  r27 : s.gpr .r27 = L.A b.iC b.oC
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
abbrev EA (K : KemLay) (L : Lay) (s₀ s : State) : Prop := KeptX [.r26, .r25, .r24] (L.RL (encW0 K)) s₀ s

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem EA.ctx {s : State} (h : EA K L s₀ s) : Ctx L s := KeptX.ctx h (by decide) hp.ctx

/-- The bytes of a part of a buffer apart from `encW0`. -/
theorem EA.bytes {s : State} (h : EA K L s₀ s) {i o l : Nat} (hs : sepAll L.sizes (i, o, l) (encW0 K) = true) :
    bytesAt s.mem (L.A i o) l = bytesAt s₀.mem (L.A i o) l := by
  have := sepAll_bounds hs
  have := hp.ctx.ok.fit i this.1
  exact Lay.bytes_keep hp.ctx.ok h.frame hs (by simp only [Lay.size] at this; omega)

theorem EA.ek {s : State} (h : EA K L s₀ s) {k n : Nat} (hk : k + n ≤ K.ekLen) :
    bytesAt s.mem (L.A b.iE (b.oE + k)) n = bytesAt s₀.mem (L.A b.iE (b.oE + k)) n :=
  EA.bytes hp h (sepAll_mono hp.sE (inB_off hk)
    (List.all_eq_true.mpr fun _ h => List.any_eq_true.mpr ⟨_, h, inB_refl _⟩))

omit hp in
theorem EA.reg {s : State} (h : EA K L s₀ s) {r : Reg} (hr : r ∈ [Reg.r30, .r29, .r31, .r27]) :
    s.gpr r = s₀.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact h.cs _ (by decide) (by decide)

/-! ## `ρ` -/

theorem enc1_ok : WP isa (copy .r30 (384 * K.k) .r31 oSeed 32) s₀ fun s =>
    EA K L s₀ s ∧ Frame (L.RL [(0, oSeed, 32)]) s₀.mem s.mem ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  have hs : sepB L.sizes (b.iE, b.oE + 384 * K.k, 32) (0, oSeed, 32) = true :=
    sepB_mono (List.all_eq_true.mp hp.sE (0, 1248, 34) (by simp)) (inB_off (by offs)) (by decide)
  refine WP.mono (copyLo hL (bo := b.oE) (by decide) (by decide) hp.r30 hp.ctx.r31 (by omega)
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
  (by decide : ∀ k < 5, PrfEk (kOf k)) K.k (by have := hK.k4; omega)

theorem enc3_ok {s₂ : State} (h₂ : EA K L s₀ s₂) (hρ : bytesAt s₂.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (ht : ∀ k < K.k, PolyIs s₂.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) :
    WP isa (K.prfLoop true 0 K.k) s₂ fun s => EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      (∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) ∧
      ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₂
  obtain ⟨c1, -, c3, -, c5, -, c7⟩ := prf_ek hK
  refine WP.mono (prfLoop_ok hK hc true (N₀ := 0) (N₁ := K.k) (by have := hK.k1; omega) (by omega)
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
  refine WP.mono (prfLoop_ok hK hc false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega) (by omega)
    (EA.bytes hp h₃ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, p⟩
  · exact h₃.trans ((k.weaken (by simp)).subL hp.ctx c2)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c4) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c6 k' hk')) (hv k' hk')

/-! ## `μ` -/

omit hp in
theorem muArgs_ok (hK : K.WF) {s : State} {P M : BitVec 64} (h31 : s.gpr .r31 = P) (h29 : s.gpr .r29 = M) :
    WP isa (.block [mov .r3 .r29, .li .r4 32, .li .r5 1, .addi .r6 .r31 (oPoly (3 * K.k + 1))]) s
      fun s' => Only s s' ∧ s'.gpr .r3 = M ∧ s'.gpr .r4 = BitVec.ofNat 64 (32 * 1) ∧
        s'.gpr .r5 = BitVec.ofNat 64 1 ∧ s'.gpr .r6 = P + BitVec.ofNat 64 (oPoly (3 * K.k + 1)) := by
  have e3 : oPoly (3 * K.k + 1) < 32768 := by offs
  prun [e3, h31, h29]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem enc5a_ok {s₄ : State} (h₄ : EA K L s₀ s₄) :
    WP isa (.block [mov .r3 .r29, .li .r4 32, .li .r5 1, .addi .r6 .r31 (oPoly (3 * K.k + 1))]) s₄
      fun s => (EA K L s₀ s ∧ s.mem = s₄.mem) ∧ s.gpr .r3 = L.A b.iM b.oM ∧
        s.gpr .r4 = BitVec.ofNat 64 (32 * 1) ∧ s.gpr .r5 = BitVec.ofNat 64 1 ∧
        s.gpr .r6 = L.A 0 (oPoly (3 * K.k + 1)) := by
  have hc := EA.ctx hp h₄
  have g29 : s₄.gpr .r29 = L.A b.iM b.oM := by rw [EA.reg h₄ (by simp), hp.r29]
  exact WP.mono (muArgs_ok hp.wf hc.r31 g29) fun s₁ ⟨o₁, a3, a4, a5, a6⟩ =>
    ⟨⟨h₄.trans (o₁.x _ _), o₁.mem⟩, a3, a4, a5, a6⟩

theorem enc5b_ok {s₄ s : State} (h₄ : EA K L s₀ s₄) (h : EA K L s₀ s ∧ s.mem = s₄.mem)
    (a3 : s.gpr .r3 = L.A b.iM b.oM) (a4 : s.gpr .r4 = BitVec.ofNat 64 (32 * 1))
    (a5 : s.gpr .r5 = BitVec.ofNat 64 1) (a6 : s.gpr .r6 = L.A 0 (oPoly (3 * K.k + 1))) :
    WP isa callDecompress s fun s' => EA K L s₀ s' ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s'.mem ∧
      PolyIs s'.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀)) := by
  have hK := hp.wf
  have hc := EA.ctx hp h.1
  have hs : sepB L.sizes (b.iM, b.oM, 32 * 1) (0, oPoly (3 * K.k + 1), 1024) = true :=
    sepB_mono (List.all_eq_true.mp hp.sM (0, 2048, 1024 * (3 * K.k + 5)) (by simp)) (inB_refl _) (by kdecide)
  refine decompressL hp.ctx.ok a3 a4 a5 a6 (by decide) hs (by rw [h.1.rd, h.1.wr]; exact hp.wM)
    hc.cw fun s' k p => ⟨?_, ?_, ?_⟩
  · exact h.1.trans ((k.x _).subL hp.ctx (by kdecide))
  · rw [← h.2]; exact k.frame
  · rw [h.2, show 32 * 1 = 32 from rfl, EA.bytes hp h₄ hp.sM] at p; exact p

end

end Enc

end VG.Proof.MlKem.PPC64LE
