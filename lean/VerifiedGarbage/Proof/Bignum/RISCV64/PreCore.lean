module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: the contract and the arithmetic

`fnContract`: `vg_rsa_public_precompute` on the registers; `PD`, the public
data of a run; `Base`, what holds from `setup` on, and `C1`, the state after
`setup`, for the proofs of correctness and constant time.

`core_ok`: from the state after `setup`, `core` loads and checks `n`, then
writes `n` and `R² mod n` to `pre` and returns 1, or zeros and returns 0
(`preOut`), changing only the arrays 0–3 and `pre`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64.Precompute VG.Proof.Mont
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-- The postcondition on `pre` and the return value. -/
def preOut (nb : List Byte) (P : Addr) (pl : Nat) (r : BitVec 64) (m : Mem) : Prop :=
  match Spec.Rsa.publicPrecompute nb with
  | some ws => r.setWidth 32 = 1 ∧ Spec.Rsa.wordsAt m P pl = ws
  | none => r.setWidth 32 = 0 ∧ Spec.Rsa.wordsAt m P pl = List.replicate pl 0

/-- The arrays 0–3 of a working space at `S`. -/
abbrev arrR (S : Addr) (w : Nat) : Region := ⟨off S hdrBytes, 32 * (w + 2)⟩

/-- `pre`, `pre_len` words at `a0`. -/
abbrev preR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩

/-- `n`, `n_len` bytes at `a2`. -/
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩

/-- The working space, `scratch_len` words at `a4`. -/
abbrev scrR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩

/-- `vg_rsa_public_precompute(pre = a0, pre_len = a1, n = a2, n_len = a3,
scratch = a4, scratch_len = a5)`. -/
def fnContract : Contract isa where
  pre s :=
    s.rd = [nR s] ∧ s.wr = [preR s, scrR s] ∧ (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (scrR s) ∧
      (nR s).Disjoint (scrR s) ∧ (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a3).toNat ∧ (s.gpr .a1).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat ∧
      Spec.Rsa.publicScratchWords (s.gpr .a3).toNat ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (s.gpr .a0) (s.gpr .a1).toNat (s'.gpr .a0)
      s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ∧
      s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5

/-! ## The public data of a run, and the state after `setup` -/

/-- The public data of a run: `pre`, `n`, the working space, `n_len`, the
working space's size in bytes and `n`'s bytes. -/
structure PD where
  P : Addr
  N : Addr
  S : Addr
  k : Nat
  Z : Nat
  nb : List Byte

/-- The words of a number of `n_len` bytes. -/
abbrev PD.w (d : PD) : Nat := (d.k + 7) / 8

/-- The registers `setup` sets for the rest of the function. -/
def baseRegs : List Reg := [.s5, .a7, .a2, .a5, .a6, .t0, .s6, .s8, .s7]

/-- What holds from `setup` on. -/
structure Base (d : PD) (s : State) : Prop where
  scr : Scr s d.S d.Z
  pre : Scr s d.P (16 * d.w)
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hZ : slot d.w 8 ≤ d.Z
  hPS : ∀ x, ofs d.S x < d.Z → 16 * d.w ≤ ofs d.P x
  len : d.nb.length = d.k
  s5 : s.gpr .s5 = d.P
  a7 : s.gpr .a7 = off d.S (slot d.w 0)
  a2 : s.gpr .a2 = off d.S (slot d.w 1)
  a5 : s.gpr .a5 = off d.S (slot d.w 2)
  a6 : s.gpr .a6 = off d.S (slot d.w 3)
  t0 : s.gpr .t0 = BitVec.ofNat 64 d.w
  s6 : s.gpr .s6 = d.S
  s8 : s.gpr .s8 = BitVec.ofNat 64 d.k
  s7 : s.gpr .s7 = d.N

theorem Base.keep {d : PD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t where
  scr := h.scr.congr k.2.2
  pre := h.pre.congr k.2.2
  k64 := h.k64
  k1024 := h.k1024
  hZ := h.hZ
  hPS := h.hPS
  len := h.len
  s5 := (k.gpr (hr _ (by decide))).trans h.s5
  a7 := (k.gpr (hr _ (by decide))).trans h.a7
  a2 := (k.gpr (hr _ (by decide))).trans h.a2
  a5 := (k.gpr (hr _ (by decide))).trans h.a5
  a6 := (k.gpr (hr _ (by decide))).trans h.a6
  t0 := (k.gpr (hr _ (by decide))).trans h.t0
  s6 := (k.gpr (hr _ (by decide))).trans h.s6
  s8 := (k.gpr (hr _ (by decide))).trans h.s8
  s7 := (k.gpr (hr _ (by decide))).trans h.s7

/-- The state after `setup`: `n`'s bytes are readable, apart from the working
space and still in memory. -/
structure C1 (d : PD) (s : State) : Prop where
  base : Base d s
  rd : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.N i) 1
  sep : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.N i ≠ x
  bytes : ∀ i (h : i < d.nb.length), s.mem (off d.N i) = d.nb[i]

theorem C1.bytesAt {d : PD} {s : State} (h : C1 d s) : Spec.Rsa.bytesAt s.mem d.N d.k = d.nb :=
  List.ext_getElem (by simp [Spec.Rsa.bytesAt, h.base.len]) fun i h1 h2 => by
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.bytes i h2


/-- Memory that changed only at offsets `[o, o + n)` of `B` changed only in
the region from `B + d` of `L` bytes that holds them. -/
theorem frame_of_outside {B : Addr} {o n d L Z : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hd : d ≤ o) (hL : o + n ≤ d + L) (hZ : d + L < Z) (hB : B.toNat + Z ≤ 2 ^ 64) :
    Frame [⟨off B d, L⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine h x ?_
  simp only [ofs]
  have e : (x - off B d).toNat = (2 ^ 64 - d + (x - B).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x B (by omega_arith)
  rw [e] at hc
  have := (x - B).isLt
  rcases Nat.lt_or_ge (x - B).toNat d with h1 | h1
  · left; omega_arith
  · right
    rw [show 2 ^ 64 - d + (x - B).toNat = (x - B).toNat - d + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)] at hc
    omega_arith

theorem frame_of_outside0 {B : Addr} {n L : Nat} {m m' : Mem} (h : Outside B 0 n m m') (hL : n ≤ L) :
    Frame [⟨B, L⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  exact h x (Or.inr (by simp only [ofs]; omega_arith))

theorem wordsVal_eq_wv (m : Mem) (P : Addr) (d W : Nat) : wordsVal m P d W = VG.Proof.Bignum.wv m P d W := by
  rw [VG.Proof.Bignum.wordsVal_read, VG.Proof.Bignum.read_eq_wv]

/-- The registers the arithmetic writes. -/
def coreRegs : List Reg :=
  [.a0, .a1, .a3, .a4, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- From the state after `setup`: `pre` and the return value, with only the
arrays and `pre` changed. -/
theorem core_ok {s : State} {P N S : Addr} {Z k w : Nat} (hs : Scr s S Z) (hp : Scr s P (16 * w))
    (hw : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024) (hZ : slot w 8 ≤ Z)
    (h5 : s.gpr .s5 = P) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (h7 : s.gpr .s7 = N)
    (ha7 : s.gpr .a7 = off S (slot w 0)) (ha2 : s.gpr .a2 = off S (slot w 1))
    (ha5 : s.gpr .a5 = off S (slot w 2)) (ha6 : s.gpr .a6 = off S (slot w 3))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hNS : ∀ i < k, ∀ x, ofs S x < Z → off N i ≠ x) (hPS : ∀ x, ofs S x < Z → 16 * w ≤ ofs P x) :
    WP isa core s fun t =>
      (preOut (Spec.Rsa.bytesAt s.mem N k) P (2 * w) (t.gpr .a0) t.mem ∧
        Frame [arrR S w, ⟨P, 16 * w⟩] s.mem t.mem) ∧ Keep coreRegs s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hw1 : 8 ≤ w := by omega_arith
  have hw' : w < 2 ^ 31 := by omega_arith
  have al := slot_al w
  unfold core
  -- `n` into array 0.
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 0) hs ha7 (by rw [h7]; simp) h8 ht0 (by omega_arith)
    (by omega_arith) hw' (by omega_arith) (al 0) (by omega_arith) hrd hNS) fun s₁ ⟨hv₁, out₁, k₁⟩ => ?_)
  have hN₁ : ∀ i < k, s₁.mem (off N i) = s.mem (off N i) := fun i hi => out₁ _ (Or.inr (by
    have := hNS i hi (off N i)
    simp only [Mont.ofs, ofs] at this ⊢
    by_contra hc; exact this (by omega) rfl))
  -- The check.
  refine WP.seq (WP.mono (check_ok (N := N) (nb := Spec.Rsa.bytesAt s.mem N k) ((k₁.gpr (r := .s7) (by decide)).trans
    (by rw [h7]; simp)) ((k₁.gpr (r := .s8) (by decide)).trans h8) hk hk' (VG.Proof.Bignum.bytesAt_length _ _ _)
    (by rw [k₁.2.1, k₁.2.2]; exact hrd) fun i hi => by
      rw [hN₁ i hi]; simp [Spec.Rsa.bytesAt, off]) fun s₂ ⟨hc₂, m₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hp₂ := hp.congr k12.2.2
  have fr₁ : Frame [arrR S w] s.mem s₂.mem := by
    rw [m₂]; exact frame_of_outside (d := hdrBytes) (L := 32 * (w + 2)) (Z := Z) (fun x hx => out₁ x hx)
      (by omega_arith) (by omega_arith) (by omega_arith) hnw
  have g : ∀ r ∈ [Reg.s5, .a2, .a5, .a6, .a7, .t0], s₂.gpr r = s.gpr r := fun r hr =>
    k12.gpr (by revert r hr; decide)
  refine WP.ite (s₂.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k = true :=
      hc₂.mp (by simpa using hb)
    have hf := VG.Proof.Bignum.valid_facts hv hk
    rw [← hw] at hf
    refine WP.seq (WP.mono (r2_ok hs₂ (by rw [g .a2 (by decide), ha2]) (by rw [g .a5 (by decide), ha5])
      (by rw [g .a6 (by decide), ha6]) (by rw [g .a7 (by decide), ha7]) (by rw [g .t0 (by decide), ht0])
      (by omega_arith) hw' (by omega_arith) (by rw [m₂, hv₁]; exact hf.2.2)
      (by rw [m₂, hv₁]; exact hf.1)) fun s₃ ⟨hx₃, out₃, k₃⟩ => ?_)
    have k13 := k12.trans k₃
    refine WP.seq (WP.mono (write_ok (P := P) (dN := slot w 0) (dX := slot w 1) (hs.congr k13.2.2)
      (hp.congr k13.2.2) (by rw [k13.gpr (r := .s5) (by decide) |>.trans h5]; simp)
      (by rw [k13.gpr (r := .a7) (by decide), ha7]) (by rw [k13.gpr (r := .a2) (by decide), ha2])
      (by rw [k13.gpr (r := .t0) (by decide), ht0]) (by omega_arith) hw' (al 0) (al 1)
      (by omega_arith) (by omega_arith) (Nat.le_refl _) hPS) fun s₄ ⟨⟨hwN, hwX, out₄⟩, k₄⟩ => ?_)
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 1 ∧ t.mem = s₄.mem) (by brun [exec_li]; rfl)
      (by rfl) (by rfl)) fun t ⟨⟨t0', tm⟩, k₅⟩ => ⟨⟨?_, ?_⟩, ((k13.trans k₄).trans k₅).mono (by decide)⟩
    · have hN0 : wordsVal s₃.mem S (slot w 0) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) := by
        rw [Outside.wordsVal out₃ (by omega_arith) (by omega_arith), m₂, hv₁]
      have hX : wordsVal s₃.mem S (slot w 1) w =
          2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) := by
        rw [hx₃, m₂, hv₁]
      rw [preOut, VG.Proof.Bignum.publicPrecompute_some (VG.Proof.Bignum.bytesAt_length _ _ _) hv, ← hw]
      refine ⟨by rw [t0']; rfl, ?_⟩
      rw [tm]
      refine VG.Proof.Bignum.wordsAt_two (fun i hi => ?_) (fun i hi => ?_)
      · exact (hwN i hi).trans (by
          show VG.Proof.Bignum.word s₃.mem S (slot w 0 + 8 * i) = _
          rw [VG.Proof.Bignum.word_eq_ofNat _ _ _ w hi, ← wordsVal_eq_wv, hN0])
      · exact (hwX i hi).trans (by
          show VG.Proof.Bignum.word s₃.mem S (slot w 1 + 8 * i) = _
          rw [VG.Proof.Bignum.word_eq_ofNat _ _ _ w hi, ← wordsVal_eq_wv, hX])
    · rw [tm]
      refine ((fr₁.mono (by simp)).trans ?_).trans ((frame_of_outside0 out₄ (Nat.le_refl _)).mono (by simp))
      exact (frame_of_outside (d := hdrBytes) (L := 32 * (w + 2)) (Z := Z) (fun x hx => out₃ x hx)
        (by omega_arith) (by omega_arith) (by omega_arith) hnw).mono (by simp)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k = false := by
      cases h : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k
      · rfl
      · exact absurd (hc₂.mpr h) (by simpa using hb)
    refine WP.seq (WP.mono (zeroPre_ok hp₂ (by rw [g .s5 (by decide), h5]; simp)
      (by rw [g .t0 (by decide), ht0]) (by omega_arith) hw' (Nat.le_refl _)) fun s₃ ⟨⟨hz, out₃⟩, k₃⟩ => ?_)
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 0 ∧ t.mem = s₃.mem) (by brun [exec_li]; rfl)
      (by rfl) (by rfl)) fun t ⟨⟨t0', tm⟩, k₄⟩ => ⟨⟨?_, ?_⟩, ((k12.trans k₃).trans k₄).mono (by decide)⟩
    · have hn : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem N k) = none := by
        simp only [Spec.Rsa.publicPrecompute, VG.Proof.Bignum.bytesAt_length, hv, Bool.false_eq_true, ite_false]
      rw [preOut, hn]
      refine ⟨by rw [t0']; rfl, ?_⟩
      rw [tm]
      apply List.ext_getElem (by simp [Spec.Rsa.wordsAt])
      intro i h1 h2
      simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact hz i (by simpa [Spec.Rsa.wordsAt] using h1)
    · rw [tm]
      exact (fr₁.mono (by simp)).trans ((frame_of_outside0 out₃ (Nat.le_refl _)).mono (by simp))

theorem core_C1 {d : PD} {s : State} (h : C1 d s) :
    WP isa core s fun t =>
      (preOut d.nb d.P (2 * d.w) (t.gpr .a0) t.mem ∧ Frame [arrR d.S d.w, ⟨d.P, 16 * d.w⟩] s.mem t.mem) ∧
        Keep coreRegs s t := by
  have hb := h.base
  have := core_ok hb.scr hb.pre rfl hb.k64 hb.k1024 hb.hZ hb.s5 hb.s8 hb.s7 hb.a7 hb.a2 hb.a5 hb.a6 hb.t0
    h.rd h.sep hb.hPS
  rwa [h.bytesAt] at this

end VG.Proof.Bignum.RISCV64.Pre
