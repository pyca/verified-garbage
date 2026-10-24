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
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Steps
public import VerifiedGarbage.Spec.P256

/-!
# Deterministic ECDSA on PPC64LE: the candidates

What the proof needs of an instance (`Rfc`): HMAC's functions (`Kit`), the
signature with a given `k` (`Core`), the code's configuration and the sizes.
Before candidate `i`, `K` and `V` are RFC 6979's (`LoopInv`); a candidate
is `V = HMAC_K(V)` (`try₁_ok`), whose leftmost `Q` bytes `core` reads as
`k` (`try₂_ok`, `try₃_ok`); then one candidate fewer and whether to go on
(`try₄_ok`), and step h.3 or the end (`branch_ok`).
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
  /-- The scalars' 32-bit words. -/
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
  hk : c.len = 4 * k
  hk12 : k ≤ 12
  hbits : Spec.Ecdsa.nBits R.E.curve = 8 * c.len
  hn₁ : c.n < 2 ^ (32 * k)
  hn₂ : 2 ^ (32 * k) < 2 * c.n
  hQD : c.len ≤ I.hashLen
  hT : 1 ≤ c.tries
  hT' : c.tries < 2 ^ 15

namespace Rfc

abbrev C (P : Rfc) : Spec.Weierstrass.Curve := P.R.E.curve
abbrev Hf (P : Rfc) : Spec.Hmac.HashFunction := P.K.hH.SH.H

end Rfc

variable {P : Rfc} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

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
  kvAtB P.Hf 1 (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.Hf 1 (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.C (candI P L m₀ i))

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

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.c.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Lay.Ok.toNat_off (hL : L.Ok) {d : Nat} (hd : d < 400) :
    (L.B + BitVec.ofNat 64 d).toNat = L.B.toNat + d := by
  have := hL.nB
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- The frame above the calls' 96 bytes is apart from what `core` writes. -/
theorem core_apart (hL : L.Ok) {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 400) :
    ∀ r ∈ [L.OUT, L.SCR, ⟨L.B, 96⟩], Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ h₁ (by omega)

/-- The frame above `K` and `V` is apart from a step's writes. -/
theorem kvW_apart (hL : L.Ok) {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 400) :
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

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) L.q) =
    Spec.Ecdsa.Rfc6979.bits2int P.C (candI P L m₀ i)

theorem lq_le (hq : L.q = P.c.len) : L.q ≤ 48 := by rw [hq, P.hk]; have := P.hk12; omega

theorem try₁_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa P.c.hmacV t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u := by
  refine WP.mono (hmacV_ok P.K P.hcH hL (lq_le hq) hc) fun u ⟨hcu, hf, hk, _, hv⟩ => ⟨hcu, hi.lt, ?_, ?_, ?_,
    hi.fails, ?_⟩
  · rw [hk, hi.k]
  · rw [hv, hi.k, hi.v]
  · rw [cnt_frame hf (kvW_apart hL (by omega) (by omega)), hi.cnt]
  · have hD : L.q ≤ P.K.H.D := by rw [hq, ← P.hD]; exact P.hQD
    have hv' : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) P.K.H.D =
        Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2 := hv.trans (by rw [hi.k, hi.v])
    have hl : (Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2).length = P.K.H.D := by
      rw [← hv', Proof.Hmac.Common.bytesAt_length]
    have hB : Spec.Ecdsa.nBits P.C = 8 * L.q := by rw [hq]; exact P.hbits
    show _ = Spec.Ecdsa.hashToInt P.C (Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2 ++ [])
    rw [List.append_nil, hashToInt_takeQ hB (by rw [hl]; exact hD), bytesAt_take _ _ hD, hv']

/-- `core`'s arguments set. -/
abbrev CoreRegs (L : Lay P.I.hashLen) (u : State) : Prop :=
  u.gpr .r3 = L.out ∧ u.gpr .r4 = L.d ∧ u.gpr .r5 = L.dg ∧ u.gpr .r6 = L.B + BitVec.ofNat 64 192 ∧
    u.gpr .r7 = L.scr

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block Cfg.coreArgs) t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u ∧ CoreRegs L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, _, h3, h4, h5, h6, h7⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.kk⟩, h3, h4, h5, h6, h7⟩

/-- After `core`: its result. -/
structure P₃ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  res : ResultIs P L (sigI P L m₀ i) u

theorem try₃_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : CoreRegs L t) :
    WP isa (.call P.c.coreN P.c.coreC) t fun u => Ctx L g lr m₀ u ∧ P₃ P L m₀ i u := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  rw [P.hcN, P.hcC]
  have hQ : P.R.E.curve.len = L.q := by rw [← P.hcl, hq]
  have hnB := hL.nB
  have hqd : L.q ≤ P.I.hashLen := by rw [hq]; exact P.hQD
  have hq48 := lq_le hq
  have hD := P.K.hH.hD64
  have hB := hL.toNat_off (d := 192) (by decide)
  have hng := hL.ng
  refine coreCall P.R h3 h4 h5 h6 h7 (by rw [hQ]; exact hL.od) (by rw [hQ]; exact hL.og.sub_right (Region.sub_prefix hqd))
    (by rw [hQ]; exact (hL.stk_OUT (d := 192) (n := L.q) (by omega)).symm) (by rw [hQ]; exact hL.oc)
    (by rw [hQ]; exact hL.dc) (by rw [hQ]; exact hL.gc.sub_left (Region.sub_prefix hqd))
    (by rw [hQ]; exact hL.stk_SCR (by omega)) (by rw [hQ]; exact hL.no) (by rw [hQ]; exact hL.nd)
    (by rw [hQ]; omega) (by rw [hQ, hB]; omega) hL.nc ?_ ?_ ?_
  · rw [hQ]
    refine hc.covers fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.DG, by simp, within_base _ hqd⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
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
      · exact .inr (.inr (Region.sub_prefix (by omega))))
    have e : Spec.Ecdsa.signWith P.R.E.curve
        (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.d P.R.E.curve.len))
        (Spec.Ecdsa.hashToInt P.R.E.curve (Spec.Ecdsa.bytesAt t.mem L.dg P.R.E.curve.len))
        (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem (L.B + BitVec.ofNat 64 192) P.R.E.curve.len)) =
        sigI P L m₀ i := by
      have hB' : Spec.Ecdsa.nBits P.C = 8 * L.q := by rw [hq]; exact P.hbits
      have eg : Spec.Ecdsa.hashToInt P.R.E.curve (Spec.Sha256.bytesAt m₀ L.dg L.q) = eOf P L m₀ := by
        show _ = Spec.Ecdsa.hashToInt P.C (Spec.Sha256.bytesAt m₀ L.dg P.I.hashLen)
        rw [hashToInt_takeQ hB' (by rw [Proof.Hmac.Common.bytesAt_length]),
          hashToInt_takeQ hB' (by rw [Proof.Hmac.Common.bytesAt_length]; exact hqd),
          List.take_of_length_le (by rw [Proof.Hmac.Common.bytesAt_length]), ← bytesAt_take _ _ hqd]
      rw [hQ]
      change Spec.Ecdsa.signWith P.R.E.curve
        (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.d L.q))
        (Spec.Ecdsa.hashToInt P.R.E.curve (Spec.Sha256.bytesAt t.mem L.dg L.q))
        (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) L.q)) = _
      rw [hc.dBytes hL (Nat.le_refl _), hc.dgBytes hL hqd, eg, hi.kk]
    rw [e, hQ] at hres
    refine ⟨hc', hi.lt, ?_, ?_, ?_, hi.fails, ?_⟩
    · exact (bytesAt_frame hf' (core_apart hL (by omega) (by omega)) (by omega)).trans hi.k
    · exact (bytesAt_frame hf' (core_apart hL (by omega) (by omega)) (by omega)).trans hi.v
    · exact (cnt_frame hf' (core_apart hL (by omega) (by omega))).trans hi.cnt
    · unfold ResultIs
      cases hs : sigI P L m₀ i <;> rw [hs] at hres <;> exact hres

/-- After the decision: whether to go on. -/
structure Mid (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.c.tries
  k : keyOf P.K L u.mem = (kvI P L m₀ i).1
  v : vOf P.K L u.mem = Spec.Hmac.hmac P.Hf (kvI P L m₀ i).1 (kvI P L m₀ i).2
  cnt : cntOf L u.mem = BitVec.ofNat 64 (P.c.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
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

theorem try₄_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g lr m₀ u ∧ Mid P L m₀ i u := by
  have hnB := hL.nB
  have hT := P.hT'
  have := hT
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
    by show u.mem.readW _ 64 = _; rw [hcnt, hci, cnt_sub hi.lt], hi.fails, hi.res.keep hc3 hout, ?_⟩
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
  have hq48 := lq_le hq
  have hq4 : L.q % 4 = 0 := by rw [hq, P.hk]; omega
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.c.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok P.K P.hcH hq.symm hL hq48 hq4 hc) fun u₅ h₅ => ?_)
    refine again_ok fun u₆ k₆ m₆ v₆ => ⟨h₅.ctx.kp hL k₆ m₆, .inr ⟨by rw [eval_nonzero, v₆]; rfl, hgo.2, ?_, ?_, ?_,
      fun j hj => ?_⟩⟩
    · rw [m₆, h₅.key, hi.k, hi.v]; rfl
    · rw [m₆, h₅.v, h₅.key, hi.k, hi.v]; rfl
    · show cntOf L u₆.mem = _
      rw [m₆, cnt_frame h₅.frame (kvW_apart hL (by omega) (by omega)), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
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
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hq h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hq h₄ p₄))))

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
