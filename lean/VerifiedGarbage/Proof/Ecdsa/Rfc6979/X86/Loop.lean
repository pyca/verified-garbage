import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Wide
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search

/-!
# Deterministic ECDSA on x86 (32-bit): the candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Loop.lean`): the values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nb` `V`s (two
if `wide`); the candidate's `k` for `core` (`cand_ok`); the loop's invariant
before candidate `i` (`LoopInv`): `K` and `V` are those before it, the count
is `8 - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1`,
branching back, or leaves the loop with the signature of candidate `i`,
which is suitable or the last (`tryOne_ok`, `loop_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The run's values -/

/-- The number of `V`s in a candidate. -/
abbrev RfcHash.nb (P : RfcHash) : Nat := if P.R.wide then 2 else 1

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.F.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.ok.hH.SH.H P.nb (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.ok.hH.SH.H P.nb (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgAddr L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .eax = 1 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => t.gpr .eax = 0 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 32 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i = 7
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

theorem hok_of (hk : CoreOk P L) : HOk P L :=
  ⟨hk.2.2.1, by rw [hk.1], fun _ => by rw [P.len]⟩

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 252, 4⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 252, 4⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by nums)
  · exact Offset.disjoint_base _ (by nums) (by nums)

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and, if two `V`s make it, the candidate above the pointers. -/
abbrev CW (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := if P.R.wide then CWW L else KVW L

theorem cw_cnt (hL : L.Ok) : ∀ r ∈ CW P L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 252, 4⟩ r := by
  cases hw : P.R.wide
  · simp only [CW, hw, Bool.false_eq_true, ite_false]; exact kvw_cnt hL
  · simp only [CW, hw, ite_true, CWW, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hL.stk_SCR (by nums)
    · exact Offset.disjoint_base _ (by nums) (by nums)
    · exact Offset.disjoint _ (by nums) (by nums) (by nums)

/-- What `core` changes: `out`, `scratch` and the stack below the frame. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B, 76⟩]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 272 + 4 * L.e) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  have := L.he
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ (by nums) (by nums)

/-- The regions the loop writes, which are apart from `core`'s digest. -/
def DgApart (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 204⟩ ∨ r = ⟨L.B, 76⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 252, 4⟩ ∨
    (P.R.wide = true ∧ r = ⟨L.B + BitVec.ofNat 64 344, 72⟩)

theorem dg_apart (hL : L.Ok) (hk : CoreOk P L) {r : Region} (h : DgApart P L r) :
    Region.Disjoint ⟨dgAddr L, P.Q⟩ r := by
  have hQ := P.sizes
  have nB := hL.nB
  cases hw : P.R.wide
  · have hLw : L.wide = false := hk.2.2.1.trans hw
    have hn := hk.2.1 hLw
    simp only [dgAddr, hLw, Bool.false_eq_true, ite_false]
    have hD : Region.Sub ⟨L.dg, P.Q⟩ L.DG := Region.sub_prefix hn
    rcases h with rfl | rfl | rfl | rfl | rfl | ⟨h, -⟩
    · exact hL.gc.sub_left hD
    · exact hL.og.symm.sub_left hD
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega))
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega))
    · exact (hL.stk_DG (by omega)).symm.sub_left hD
    · rw [hw] at h; exact absurd h (by decide)
  · obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hw
    have hLw : L.wide = true := hk.2.2.1.trans hw
    have he : L.e = 36 := by rw [L.ew, hLw]; rfl
    simp only [dgAddr, hLw, ite_true]
    rcases h with rfl | rfl | rfl | rfl | rfl | ⟨-, rfl⟩
    · exact hL.stk_SCR (by omega)
    · exact hL.stk_OUT (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem DgOk.frame {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨dgAddr L, P.Q⟩ r) : DgOk P L m₀ m' := by
  have hQ : P.Q ≤ 72 := by nums
  unfold DgOk; rw [bytesAt_frame hf hd (by omega)]; exact h

theorem DgOk.frameOf (hL : L.Ok) (hk : CoreOk P L) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, DgApart P L r) : DgOk P L m₀ m' :=
  h.frame hf fun r hr => dg_apart hL hk (hd r hr)

theorem cnt_sub {i : Nat} (hi : i < 8) : BitVec.ofNat 32 (8 - i) - 1 = BitVec.ofNat 32 (8 - (i + 1)) := by
  have : ∀ i < 8, BitVec.ofNat 32 (8 - i) - 1 = BitVec.ofNat 32 (8 - (i + 1)) := by decide
  exact this i hi

theorem cnt_ne {i : Nat} (hi : i < 8) : BitVec.ofNat 32 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8 := by
  have : ∀ i < 8, (BitVec.ofNat 32 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8) := by decide
  exact this i hi

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- `core`'s signature is the candidate's: it reads the private key, its
digest, and `k`, whose number is `bits2int` of the candidate. -/
theorem coreSig_eq (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kAddr L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  have e₄ : Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := hc.dBytes hL (by rw [hk.1])
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, xOf]
  rw [show Spec.Sha256.bytesAt t.mem (dgAddr L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (dgAddr L) P.Q from rfl,
    hdg, show Spec.Sha256.bytesAt t.mem L.d P.R.E.C.len = Spec.Sha256.bytesAt t.mem L.d P.Q from rfl, e₄,
    show Spec.Sha256.bytesAt t.mem (kAddr L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (kAddr L) P.Q from rfl, hkv]

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    t.gpr .eax = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `rax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .eax = t.gpr .eax)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## The candidate -/

theorem genT_one (H : Spec.Hmac.HashFunction) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT H K 1 V = (Spec.Hmac.hmac H K V ++ [], Spec.Hmac.hmac H K V) := rfl

theorem genT_two (H : Spec.Hmac.HashFunction) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT H K 2 V =
      (Spec.Hmac.hmac H K V ++ (Spec.Hmac.hmac H K (Spec.Hmac.hmac H K V) ++ []),
        Spec.Hmac.hmac H K (Spec.Hmac.hmac H K V)) := rfl

/-- The candidate: `V = HMAC_K(V)` (twice if `wide`), and `k`, whose number
is `bits2int` of the candidate, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW P L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).1 := by
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
    have hLw : L.wide = false := hk.2.2.1.trans hw
    simp only [RfcHash.nb, CW, hw, hLw, Bool.false_eq_true, ite_false, kAddr]
    have hc' : (cfgOf P).cand = (cfgOf P).hmacV := by simp only [Cfg.cand, cfgOf, hw]; rfl
    rw [hc', genT_one]
    refine WP.mono (hmacV_ok hL hk.2.2.1 hc) fun u ⟨hcu, hf, hk', hv⟩ => ⟨hcu, hf, hk', hv, ?_⟩
    rw [Spec.Ecdsa.Rfc6979.bits2int, List.append_nil, hashToInt_takeQ hB (by rw [mac_length]; exact hQD)]
    refine congrArg Spec.Weierstrass.ofBytes ?_
    rw [bytesAt_take _ _ hQD]
    exact congrArg (List.take P.Q) hv
  · have hLw : L.wide = true := hk.2.2.1.trans hw
    have hl := P.R.nBits_len
    simp only [RfcHash.nb, CW, hw, hLw, ite_true, kAddr]
    rw [genT_two]
    refine WP.mono (candW_ok hL hk.2.2.1 hw hc) fun u ⟨hcu, hf, hk', hv, hb⟩ => ⟨hcu, hf, hk', hv, ?_⟩
    obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    rw [hb, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
      (by simp only [List.length_append, mac_length, List.length_nil]; omega), List.append_nil,
      ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
        have := ofBytes_lt ((P.mac (kOf P L t.mem) (vOf P L t.mem) ++
          P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem))).take P.Q)
        rwa [List.length_take, Nat.min_eq_left (by simp only [List.length_append, mac_length]; omega)] at this)),
      show P.R.sh = 8 * P.R.E.C.len - _ from hl.2.2]

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nb (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 32 (8 - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval .ne u = some (decide (sigI P L m₀ i = none ∧ i + 1 < 8))

theorem kvw_apart : ∀ r ∈ KVW L, DgApart P L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem cw_apart : ∀ r ∈ CW P L, DgApart P L r := by
  cases hw : P.R.wide
  · simp only [CW, hw, Bool.false_eq_true, ite_false]; exact kvw_apart
  · simp only [CW, hw, ite_true, CWW, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp [DgApart, hw]

theorem corew_apart : ∀ r ∈ CoreW L, DgApart P L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem try₁_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hk hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_frame hf₁ (cw_cnt hL)).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hk hf₁ cw_apart, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) :
    WP isa (.block (Cfg.coreArgs P.R.wide)) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ CoreRegs L u :=
  hk.2.2.1 ▸ WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, hdi, hsi, hdx, hcx, h8⟩

theorem try₃_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : CoreRegs L t) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC)
      (.pop .ecx 5)) t fun u => Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok (P := P) hL hk hc ha) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hk hc hi.dg hi.kk] at hr₃
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by nums) (by nums)) (by nums)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by nums) (by nums)) (by nums)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by nums) (by nums))).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hk hf₃ corew_apart, hr₃⟩

theorem try₄_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails,
    hi.dg.frameOf hL hk hf₄ (by simp [DgApart]), ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by nums)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))
  · show u₄.zf.map (!·) = _
    rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [Option.map_some, Bool.not_not, hi.res.eax_zero, cnt_ne hi.lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite .ne (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < 8
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL (hok_of hk) hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨by show u₆.zf.map _ = _; rw [hz₆]; rfl, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [hm₆]; exact hi.dg.frameOf hL hk hf₅ kvw_apart
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨by show u₅.zf.map _ = _; rw [hz₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < 8 := fun h => hgo ⟨hs, h⟩; omega)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hk hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL hk h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hk h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hk h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hk h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.X86
