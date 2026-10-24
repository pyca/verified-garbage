module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Steps
public import VerifiedGarbage.Spec.P256

/-!
# Deterministic ECDSA on PPC64LE: the candidates

What the proof needs of an instance (`Rfc`): HMAC's functions (`Kit`), the
signature with a given `k` (`Core`), the code's configuration and the sizes.
Before candidate `i`, `K` and `V` are RFC 6979's and the digest `core`
reads is the digest's integer (`LoopInv`); a candidate is `V = HMAC_K(V)`,
twice if `wide` (`nb`, `cand_ok`), whose number `core` reads as `k`
(`try₁_ok`, `try₂_ok`, `try₃_ok`); then one candidate fewer and whether to
go on (`try₄_ok`), and step h.3 or the end (`branch_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB hashToInt_takeQ)

/-- What the proof needs of an instance. -/
structure Rfc where
  K : Kit
  R : Core
  c : Cfg
  I : Spec.Ecdsa.Rfc6979.Instance
  /-- The scalars' 32-bit words, unless `wide`. -/
  k : Nat
  hE : I.ecdsa = R.E
  hHash : I.hash = K.hH.SH.H
  hD : I.hashLen = K.H.D
  hcH : c.H = K.hm
  hcN : c.coreN = R.N
  hcC : c.coreC = R.C
  hcl : c.len = R.E.curve.len
  hcn : c.n = R.E.curve.n
  hct : c.tries = I.tries
  /-- Unless `wide`: scalars of `k` 32-bit words, at most 16, of `8 Q` bits,
  with `n` above half their range. -/
  hk : c.wide = false → c.len = 4 * k
  hk16 : c.wide = false → k ≤ 16
  hbits : c.wide = false → Spec.Ecdsa.nBits R.E.curve = 8 * c.len
  hn₁ : c.wide = false → c.n < 2 ^ (32 * k)
  hn₂ : c.wide = false → 2 ^ (32 * k) < 2 * c.n
  /-- If `wide`: P-521's sizes, with SHA-512's. -/
  hW : c.wide = true → c.H.D = 64 ∧ c.len = 66 ∧ Spec.Ecdsa.nBits R.E.curve = 521
  hT : 1 ≤ c.tries
  hT' : c.tries < 2 ^ 15

namespace Rfc

abbrev C (P : Rfc) : Spec.Weierstrass.Curve := P.R.E.curve
abbrev Hf (P : Rfc) : Spec.Hmac.HashFunction := P.K.hH.SH.H

/-- The number of `V`s in a candidate. -/
abbrev nb (P : Rfc) : Nat := if P.c.wide then 2 else 1

theorem hcD (P : Rfc) : P.c.H.D = P.I.hashLen := by rw [P.hcH, P.hD]; rfl

/-- Unless `wide`, the scalars are no longer than the hash. -/
theorem hQD (P : Rfc) (hw : P.c.wide = false) : P.c.len ≤ P.I.hashLen := by
  have h : ¬ P.c.H.D < P.c.len := of_decide_eq_false hw
  rw [← P.hcD]; omega

theorem hsh (P : Rfc) (hw : P.c.wide = true) : P.c.sh = 7 := by
  obtain ⟨-, hl, hb⟩ := P.hW hw
  simp only [Spec.Ecdsa.nBits] at hb
  unfold Cfg.sh; rw [hl, P.hcn]; omega

theorem hcw (P : Rfc) (hw : P.c.wide = true) : P.c.w = 9 := by
  unfold Cfg.w; rw [(P.hW hw).2.1]

end Rfc

variable {P : Rfc} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## The sizes -/

theorem wideL (hq : L.q = P.c.len) : L.wide = P.c.wide := (L.wide_eq hq.symm P.hcD).symm

/-- Unless `wide`: scalars of at most 64 bytes, a multiple of 4, no longer
than the hash, of `8 Q` bits. -/
theorem narrow_q (hq : L.q = P.c.len) (hw : L.wide = false) :
    L.q ≤ 64 ∧ L.q % 4 = 0 ∧ L.q ≤ P.I.hashLen ∧ Spec.Ecdsa.nBits P.C = 8 * L.q := by
  have hcw : P.c.wide = false := (wideL hq).symm.trans hw
  have := P.hk16 hcw
  refine ⟨by rw [hq, P.hk hcw]; omega, by rw [hq, P.hk hcw]; omega, by rw [hq]; exact P.hQD hcw, ?_⟩
  rw [hq]; exact P.hbits hcw

/-- If `wide`: P-521's sizes, with SHA-512's, and the frame's 144 bytes at its top. -/
theorem wide_q (hq : L.q = P.c.len) (hw : L.wide = true) :
    L.q = 66 ∧ P.I.hashLen = 64 ∧ L.e = 144 ∧ Spec.Ecdsa.nBits P.C = 521 := by
  have hcw : P.c.wide = true := (wideL hq).symm.trans hw
  obtain ⟨hD, hl, hb⟩ := P.hW hcw
  refine ⟨by rw [hq, hl], by rw [← P.hcD, hD], ?_, hb⟩
  simp only [Lay.e, Lay.hHigh, hw, Bool.not_true, Bool.false_and, extra, ite_true]

theorem lq_le (hq : L.q = P.c.len) : L.q ≤ 66 := by
  cases hw : L.wide
  · have := (narrow_q hq hw).1; omega
  · exact Nat.le_of_eq (wide_q hq hw).1

theorem lq_ok (hq : L.q = P.c.len) (hw : L.wide = false) : L.HOk := L.hOk (narrow_q hq hw).1 hw

theorem lfar (hq : L.q = P.c.len) : L.HFar := by
  cases hw : L.wide
  · exact (lq_ok hq hw).far
  · exact L.hFar_wide hw (by have := (wide_q hq hw).1; omega)

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d L.q)
abbrev hBOf (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.I.hashLen
abbrev eOf (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.C P.Hf P.I.hashLen (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.Hf P.nb (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.Hf P.nb (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.C (candI P L m₀ i))

/-- Where `core` reads the digest: `digest`, or, if `wide`, the digest
shifted left at the frame's top. -/
abbrev dgAddr {dn : Nat} (L : Lay dn) : Addr := if L.wide then L.B + BitVec.ofNat 64 352 else L.dg

/-- Where `core` reads `k`: `V`, or, if `wide`, the candidate at the frame's top. -/
abbrev kAddr {dn : Nat} (L : Lay dn) : Addr :=
  if L.wide then L.B + BitVec.ofNat 64 424 else L.B + BitVec.ofNat 64 192

/-- The digest `core` reads is the digest's integer. -/
def DgOk (P : Rfc) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.C (Spec.Sha256.bytesAt m (dgAddr L) L.q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : Rfc) (L : Lay P.I.hashLen) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .r3).setWidth 32 = (1 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * L.q) = Spec.Ecdsa.encode P.C rs
  | none => (t.gpr .r3).setWidth 32 = (0 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * L.q) = List.replicate (2 * L.q) 0

/-- The candidates left, in the frame. -/
abbrev cntOf {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 304) 64

/-- Before candidate `i`. -/
structure LoopInv (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L t.mem = (kvI P L m₀ i).1
  v : vOf P.K L t.mem = (kvI P L m₀ i).2
  cnt : cntOf L t.mem = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.c.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Lay.Ok.toNat_off (hL : L.Ok) {d : Nat} (hd : d < 400 + L.e) :
    (L.B + BitVec.ofNat 64 d).toNat = L.B.toNat + d := by
  have := hL.nB
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- The frame above the calls' 96 bytes is apart from what `core` writes. -/
theorem core_apart (hL : L.Ok) {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 400 + L.e) :
    ∀ r ∈ [L.OUT, L.SCR, ⟨L.B, 96⟩], Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ h₁ (by omega)

/-- The frame above `K` and `V` is apart from a step's writes. -/
theorem kvW_apart (hL : L.Ok) {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 400 + L.e) :
    ∀ r ∈ kvW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [kvW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem cnt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 304, 8⟩ r) : cntOf L m' = cntOf L m :=
  hf.readW (r := ⟨L.B + BitVec.ofNat 64 304, 8⟩) (w := 64)
    (by simpa only [Nat.reduceDiv] using Region.contains_self (L.B + BitVec.ofNat 64 304) 8) hd (by decide)

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t)
    (ha : (t'.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * L.q) = Spec.Sha256.bytesAt t.mem L.out (2 * L.q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-- What a candidate changes: a step's writes, and, if `wide`, the
candidate at the frame's top. -/
abbrev CW (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  if P.c.wide then
    [⟨L.scr, 8192⟩, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 424, 72⟩]
  else kvW L

theorem cw_cnt (hL : L.Ok) (hq : L.q = P.c.len) :
    ∀ r ∈ CW P L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 304, 8⟩ r := by
  have := hL.nB
  cases hw : P.c.wide
  · simp only [CW, hw, Bool.false_eq_true, ite_false]
    exact kvW_apart hL (by omega) (by omega)
  · have he := (wide_q hq ((wideL hq).trans hw)).2.2.1
    simp only [CW, hw, ite_true, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hL.stk_SCR (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The digest `core` reads is apart from what the loop writes: `out`,
`scratch`, the calls' stack, `K`, `V`, the count and the candidate. -/
theorem dg_apart (hL : L.Ok) (hq : L.q = P.c.len) {r : Region}
    (h : r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨ r = ⟨L.B, 96⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨
      r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨ (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩)) :
    Region.Disjoint ⟨dgAddr L, L.q⟩ r := by
  have := hL.nB
  cases hw : L.wide
  · have hqd := (narrow_q hq hw).2.2.1
    have hD : Region.Sub ⟨L.dg, L.q⟩ L.DG := Region.sub_prefix hqd
    simp only [dgAddr, hw, Bool.false_eq_true, ite_false]
    rcases h with rfl | rfl | rfl | rfl | rfl | ⟨h, -⟩
    · exact hL.og.symm.sub_left hD
    · exact hL.gc.sub_left hD
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega))
    · exact (hL.kg.symm.sub_left hD).sub_right (Offset.sub_base _ (by omega))
    · exact (hL.kg.symm.sub_left hD).sub_right (Offset.sub_base _ (by omega))
    · rw [hw] at h; exact absurd h (by decide)
  · obtain ⟨hq66, -, he, -⟩ := wide_q hq hw
    simp only [dgAddr, hw, ite_true]
    rcases h with rfl | rfl | rfl | rfl | rfl | ⟨-, rfl⟩
    · exact hL.stk_OUT (by omega)
    · exact hL.stk_SCR (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem DgOk.frame (hL : L.Ok) (hq : L.q = P.c.len) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨ r = ⟨L.B, 96⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨
      r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨ (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩)) :
    DgOk P L m₀ m' := by
  have := lq_le hq
  unfold DgOk; rw [bytesAt_frame hf (fun r hr => dg_apart hL hq (hd r hr)) (by omega)]; exact h

theorem kvW_dg : ∀ r ∈ kvW L, r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨ r = ⟨L.B, 96⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨
    (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩) := by
  simp only [kvW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> simp

theorem cw_dg (hq : L.q = P.c.len) : ∀ r ∈ CW P L, r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨ r = ⟨L.B, 96⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨
    (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩) := by
  cases hw : P.c.wide
  · simp only [CW, hw, Bool.false_eq_true, ite_false]; exact kvW_dg
  · have hLw : L.wide = true := (wideL hq).trans hw
    simp only [CW, hw, ite_true, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp [hLw]

theorem core_dg : ∀ r ∈ [L.OUT, L.SCR, ⟨L.B, 96⟩], r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨ r = ⟨L.B, 96⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨
    (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> simp

theorem cnt_dg : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 304, 8⟩ : Region)], r = L.OUT ∨ r = ⟨L.scr, 8192⟩ ∨
    r = ⟨L.B, 96⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 128, 128⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 304, 8⟩ ∨
    (L.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 424, 72⟩) := by
  simp only [List.mem_singleton]
  rintro r rfl; simp

/-! ## The candidate -/

theorem genT_one (H : Spec.Hmac.HashFunction) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT H K 1 V = (Spec.Hmac.hmac H K V ++ [], Spec.Hmac.hmac H K V) := rfl

theorem genT_two (H : Spec.Hmac.HashFunction) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT H K 2 V =
      (Spec.Hmac.hmac H K V ++ (Spec.Hmac.hmac H K (Spec.Hmac.hmac H K V) ++ []),
        Spec.Hmac.hmac H K (Spec.Hmac.hmac H K V)) := rfl

/-- The candidate: `V = HMAC_K(V)` (twice if `wide`), and `k`, whose number
is `bits2int` of the candidate, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa P.c.cand t fun u => Ctx L g lr m₀ u ∧ Frame (CW P L) t.mem u.mem ∧
      keyOf P.K L u.mem = keyOf P.K L t.mem ∧
      vOf P.K L u.mem = (Spec.Ecdsa.Rfc6979.genT P.Hf (keyOf P.K L t.mem) P.nb (vOf P.K L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) L.q) =
        Spec.Ecdsa.Rfc6979.bits2int P.C
          (Spec.Ecdsa.Rfc6979.genT P.Hf (keyOf P.K L t.mem) P.nb (vOf P.K L t.mem)).1 := by
  cases hw : L.wide
  · obtain ⟨-, -, hqd, hB⟩ := narrow_q hq hw
    have hcw : P.c.wide = false := (wideL hq).symm.trans hw
    simp only [CW, Rfc.nb, kAddr, hcw, hw, Bool.false_eq_true, ite_false, Cfg.cand, genT_one]
    refine WP.mono (hmacV_ok P.K P.hcH hL (lfar hq) hc) fun u ⟨hcu, hf, hk, _, hv⟩ => ⟨hcu, hf, hk, hv, ?_⟩
    have hD : L.q ≤ P.K.H.D := by rw [← P.hD]; exact hqd
    have hl : (Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem) (vOf P.K L t.mem)).length = P.K.H.D := by
      rw [← hv, Proof.Hmac.Common.bytesAt_length]
    rw [Spec.Ecdsa.Rfc6979.bits2int, List.append_nil, hashToInt_takeQ hB (by rw [hl]; exact hD),
      bytesAt_take _ _ hD, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) P.K.H.D = _ from hv]
  · obtain ⟨hq66, -, he, hB⟩ := wide_q hq hw
    have hcw : P.c.wide = true := (wideL hq).symm.trans hw
    obtain ⟨hcD, hcl, -⟩ := P.hW hcw
    simp only [CW, Rfc.nb, kAddr, hcw, hw, ite_true, genT_two]
    refine WP.mono (candW_ok P.K P.hcH hcw hcl hcD (P.hcw hcw) (P.hsh hcw) he (lfar hq) hL hc)
      fun u ⟨hcu, hf, hk, hv, hl₁, hb⟩ => ⟨hcu, hf, hk, hv, ?_⟩
    have hl₂ : (Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem)
        (Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem) (vOf P.K L t.mem))).length = 64 := by
      rw [← hv, Proof.Hmac.Common.bytesAt_length, ← P.hD, (wide_q hq hw).2.1]
    rw [hq66, hb, Spec.Ecdsa.Rfc6979.bits2int, List.append_nil,
      hashToInt_takeR (R := 66) (by omega) (by simp only [List.length_append, hl₁, hl₂]; omega),
      show 8 * 66 - Spec.Ecdsa.nBits P.C = 7 by omega]
    refine Rfc6979.ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ?_)
    have := Rfc6979.ofBytes_lt ((Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem) (vOf P.K L t.mem) ++
      Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem) (Spec.Hmac.hmac P.Hf (keyOf P.K L t.mem) (vOf P.K L t.mem))).take 66)
    rwa [List.length_take, List.length_append, hl₁, hl₂, show min 66 (64 + 64) = 66 from rfl] at this

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = (Spec.Ecdsa.Rfc6979.genT P.Hf (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) L.q) =
    Spec.Ecdsa.Rfc6979.bits2int P.C (candI P L m₀ i)

theorem try₁_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa P.c.cand t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hq hc) fun u ⟨hcu, hf, hk, hv, hb⟩ => ⟨hcu, hi.lt, hk.trans hi.k,
    by rw [hv, hi.k, hi.v], (cnt_frame hf (cw_cnt hL hq)).trans hi.cnt, hi.fails,
    hi.dg.frame hL hq hf (cw_dg hq), by rw [hb, hi.k, hi.v]; rfl⟩

/-- `core`'s arguments set. -/
abbrev CoreRegs (L : Lay P.I.hashLen) (u : State) : Prop :=
  u.gpr .r3 = L.out ∧ u.gpr .r4 = L.d ∧ u.gpr .r5 = dgAddr L ∧ u.gpr .r6 = kAddr L ∧ u.gpr .r7 = L.scr

theorem try₂_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) :
    WP isa (.block (Cfg.coreArgs P.c.wide)) t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u ∧ CoreRegs L u :=
  WP.mono (coreArgs_ok hL P.c.wide hc) fun _ ⟨hc₂, hm₂, _, h3, h4, h5, h6, h7⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, h3, h4,
      by rw [h5, ← wideL hq], by rw [h6, ← wideL hq], h7⟩

/-- What `core`'s call needs of its regions. -/
theorem core_regions (hL : L.Ok) (hq : L.q = P.c.len) :
    Region.Disjoint ⟨L.out, 2 * L.q⟩ ⟨L.d, L.q⟩ ∧ Region.Disjoint ⟨L.out, 2 * L.q⟩ ⟨dgAddr L, L.q⟩ ∧
    Region.Disjoint ⟨L.out, 2 * L.q⟩ ⟨kAddr L, L.q⟩ ∧ Region.Disjoint ⟨L.out, 2 * L.q⟩ ⟨L.scr, 8192⟩ ∧
    Region.Disjoint ⟨L.d, L.q⟩ ⟨L.scr, 8192⟩ ∧ Region.Disjoint ⟨dgAddr L, L.q⟩ ⟨L.scr, 8192⟩ ∧
    Region.Disjoint ⟨kAddr L, L.q⟩ ⟨L.scr, 8192⟩ ∧
    L.out.toNat + 2 * L.q ≤ 2 ^ 64 ∧ L.d.toNat + L.q ≤ 2 ^ 64 ∧ (dgAddr L).toNat + L.q ≤ 2 ^ 64 ∧
    (kAddr L).toNat + L.q ≤ 2 ^ 64 ∧ L.scr.toNat + 8192 ≤ 2 ^ 64 ∧
    ∀ r ∈ [(⟨L.d, L.q⟩ : Region), ⟨dgAddr L, L.q⟩, ⟨kAddr L, L.q⟩, L.OUT, L.SCR],
      ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R := by
  have hnB := hL.nB
  have hng := hL.ng
  have hdo : Region.Disjoint ⟨dgAddr L, L.q⟩ L.OUT := dg_apart hL hq (.inl rfl)
  have hds : Region.Disjoint ⟨dgAddr L, L.q⟩ ⟨L.scr, 8192⟩ := dg_apart hL hq (.inr (.inl rfl))
  have hql := lq_le hq
  have hkk : (kAddr L).toNat + L.q ≤ 2 ^ 64 ∧ Region.Disjoint ⟨kAddr L, L.q⟩ L.OUT ∧
      Region.Disjoint ⟨kAddr L, L.q⟩ L.SCR ∧ ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨kAddr L, L.q⟩ R := by
    cases hw : L.wide
    · have hq64 := (narrow_q hq hw).1
      simp only [kAddr, hw, Bool.false_eq_true, ite_false]
      exact ⟨by rw [hL.toNat_off (by omega)]; omega, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · obtain ⟨hq66, -, he, -⟩ := wide_q hq hw
      simp only [kAddr, hw, ite_true]
      exact ⟨by rw [hL.toNat_off (by omega)]; omega, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        L.FR, by simp, within_fr _ (by omega) (by omega)⟩
  have hdd : (dgAddr L).toNat + L.q ≤ 2 ^ 64 ∧ ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨dgAddr L, L.q⟩ R := by
    cases hw : L.wide
    · have hqd := (narrow_q hq hw).2.2.1
      simp only [dgAddr, hw, Bool.false_eq_true, ite_false]
      exact ⟨by omega, L.DG, by simp, within_base _ hqd⟩
    · obtain ⟨hq66, -, he, -⟩ := wide_q hq hw
      simp only [dgAddr, hw, ite_true]
      exact ⟨by rw [hL.toNat_off (by omega)]; omega, L.FR, by simp, within_fr _ (by omega) (by omega)⟩
  obtain ⟨hk₁, hk₂, hk₃, hk₄⟩ := hkk
  obtain ⟨hd₁, hd₂⟩ := hdd
  refine ⟨hL.od, hdo.symm, hk₂.symm, hL.oc, hL.dc, hds, hk₃, hL.no, hL.nd, hd₁, hk₁, hL.nc, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨L.D, by simp, within_base _ (Nat.le_refl _)⟩
  · exact hd₂
  · exact hk₄
  · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩

/-- After `core`: its result. -/
structure P₃ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = (Spec.Ecdsa.Rfc6979.genT P.Hf (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

theorem try₃_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : CoreRegs L t) :
    WP isa (.call P.c.coreN P.c.coreC) t fun u => Ctx L g lr m₀ u ∧ P₃ P L m₀ i u := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  rw [P.hcN, P.hcC]
  have hQ : P.R.E.curve.len = L.q := by rw [← P.hcl, hq]
  have hnB := hL.nB
  have hD := P.K.hH.hD64
  have hql := lq_le hq
  obtain ⟨o₁, o₂, o₃, o₄, c₁, c₂, c₃, n₁, n₂, n₃, n₄, n₅, hcov⟩ := core_regions hL hq
  refine coreCall P.R h3 h4 h5 h6 h7 (by rw [hQ]; exact o₁) (by rw [hQ]; exact o₂) (by rw [hQ]; exact o₃)
    (by rw [hQ]; exact o₄) (by rw [hQ]; exact c₁) (by rw [hQ]; exact c₂) (by rw [hQ]; exact c₃)
    (by rw [hQ]; exact n₁) (by rw [hQ]; exact n₂) (by rw [hQ]; exact n₃) (by rw [hQ]; exact n₄) n₅
    (by rw [hQ]; exact hc.covers hcov) ?_ ?_
  · rw [hQ]
    refine hc.coversW fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
  · intro s' hrd hwr hsp hf hcs hres
    rw [hc.sp, Lay.below96] at hf
    have hf' : Frame [L.OUT, L.SCR, ⟨L.B, 96⟩] t.mem s'.mem := by have := hf; rw [hQ] at this; exact this
    have hc' : Ctx L g lr m₀ s' := hc.keep hL hrd hwr hsp hcs hf' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact .inl fun _ h => h
      · exact .inr (.inl fun _ h => h)
      · exact .inr (.inr (.inl (Region.sub_prefix (by omega)))))
    have e : Spec.Ecdsa.signWith P.R.E.curve
        (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.d P.R.E.curve.len))
        (Spec.Ecdsa.hashToInt P.R.E.curve (Spec.Ecdsa.bytesAt t.mem (dgAddr L) P.R.E.curve.len))
        (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem (kAddr L) P.R.E.curve.len)) =
        sigI P L m₀ i := by
      rw [hQ]
      change Spec.Ecdsa.signWith P.R.E.curve
        (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.d L.q))
        (Spec.Ecdsa.hashToInt P.R.E.curve (Spec.Sha256.bytesAt t.mem (dgAddr L) L.q))
        (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kAddr L) L.q)) = _
      rw [hc.dBytes hL (Nat.le_refl _), show Spec.Ecdsa.hashToInt P.R.E.curve
        (Spec.Sha256.bytesAt t.mem (dgAddr L) L.q) = eOf P L m₀ from hi.dg, hi.kk]
    rw [e, hQ] at hres
    refine ⟨hc', hi.lt, ?_, ?_, ?_, hi.fails, hi.dg.frame hL hq hf' core_dg, ?_⟩
    · exact (bytesAt_frame hf' (core_apart hL (by omega) (by omega)) (by omega)).trans hi.k
    · exact (bytesAt_frame hf' (core_apart hL (by omega) (by omega)) (by omega)).trans hi.v
    · exact (cnt_frame hf' (core_apart hL (by omega) (by omega))).trans hi.cnt
    · unfold ResultIs
      cases hs : sigI P L m₀ i <;> rw [hs] at hres <;> exact hres

/-- After the decision: whether to go on. -/
structure Mid (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = (Spec.Ecdsa.Rfc6979.genT P.Hf (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval (.nonzero .d .r12) u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.c.tries))

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 64 (T - i) - 1 = BitVec.ofNat 64 (T - (i + 1)) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega)

theorem and_one_of {x : BitVec 64} {b : BitVec 32} (h : x.setWidth 32 = b) (hb : b.toNat ≤ 1) :
    x &&& 1 = BitVec.ofNat 64 b.toNat :=
  BitVec.eq_of_toNat_eq (by
    have e := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth] at e
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega)

theorem try₄_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g lr m₀ u ∧ Mid P L m₀ i u := by
  have hnB := hL.nB
  have hT := P.hT'
  have := hT
  have hql := lq_le hq
  refine WP.mono (goOn_ok hL hc) fun u ⟨hcu, K, hf, hcnt, h12⟩ => ?_
  have hci : t.mem.readW (L.B + BitVec.ofNat 64 304) 64 = BitVec.ofNat 64 (P.c.tries - i) := hi.cnt
  have hd : ∀ {d n : Nat}, 96 ≤ d → d + n ≤ 304 →
      ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 304, 8⟩ : Region)], Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have hD := P.K.hH.hD64
  have hc3 : (u.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32 := by rw [K.gpr _ (by decide)]
  have hout : Spec.Sha256.bytesAt u.mem L.out (2 * L.q) = Spec.Sha256.bytesAt t.mem L.out (2 * L.q) :=
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega)).symm) (by have := hL.no; omega)
  refine ⟨hcu, hi.lt, (bytesAt_frame hf (hd (by omega) (by omega)) (by omega)).trans hi.k,
    (bytesAt_frame hf (hd (by omega) (by omega)) (by omega)).trans hi.v,
    by show u.mem.readW _ 64 = _; rw [hcnt, hci, cnt_sub hi.lt], hi.fails, hi.dg.frame hL hq hf cnt_dg,
    hi.res.keep hc3 hout, ?_⟩
  rw [eval_nonzero, h12, hci, cnt_sub hi.lt]
  have hres := hi.res
  unfold ResultIs at hres
  cases hs : sigI P L m₀ i <;> rw [hs] at hres
  · rw [and_one_of hres.1 (by decide)]
    have : (BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 &&& BitVec.ofNat 64 (P.c.tries - (i + 1))) =
        BitVec.ofNat 64 (P.c.tries - (i + 1)) := by
      rw [show BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
    rw [this, bne, ofNat_beq_zero (by omega)]
    simp only [true_and, Option.some.injEq]
    rw [← decide_not]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · rw [and_one_of hres.1 (by decide)]
    simp

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : Mid P L m₀ i t) :
    WP isa (.ite (.nonzero .d .r12) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' =>
      Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.c.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok P.K P.hcH hq.symm hL (lfar hq) (by have := lq_le hq; omega) hc)
      fun u₅ h₅ => ?_)
    refine again_ok fun u₆ k₆ m₆ v₆ => ⟨h₅.ctx.kp hL k₆ m₆, .inr ⟨by rw [eval_nonzero, v₆]; rfl, hgo.2, ?_, ?_, ?_,
      fun j hj => ?_, ?_⟩⟩
    · rw [m₆, h₅.key, hi.k, hi.v]; rfl
    · rw [m₆, h₅.v, h₅.key, hi.k, hi.v]; rfl
    · show cntOf L u₆.mem = _
      rw [m₆, cnt_frame h₅.frame (kvW_apart hL (by omega) (by omega)), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [m₆]; exact hi.dg.frame hL hq h₅.frame kvW_dg
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine stop_ok fun u₅ k₅ m₅ v₅ => ⟨hc.kp hL k₅ m₅, .inl ⟨by rw [eval_nonzero, v₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep (by rw [k₅.gpr _ (by decide)]) (by rw [m₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.c.tries := fun h => hgo ⟨hs, h⟩; omega)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa P.c.tryOne t fun t' => Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hq hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL hq h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hq h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hq h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hq h₄ p₄))))

theorem loop_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t)
    (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop P.c.tryOne (.nonzero .d .r12)) t fun t' => Ctx L g lr m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g lr m₀ s ∧ LoopInv P L m₀ (P.c.tries - n) s ∧
    n ≤ P.c.tries) ?_ P.c.tries t ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hq hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show P.c.tries - (n - 1) = P.c.tries - n + 1 by omega]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
