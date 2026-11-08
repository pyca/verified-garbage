module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the
call of `core` with the candidate (`core_ok`); the loop's invariant before
candidate `i` (`LoopInv`): `K` and `V` are those before it, the count is
`tries - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1` or
leaves the loop with the signature of candidate `i`, which is suitable or
the last (`tryOne_ok`, `loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.v.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  Spec.Ecdsa.hashToInt P.R.C.E.curve (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.C.E.curve P.v.ok.SH.H P.v.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.v.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.v.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.C.E.curve (xOf P L m₀) (eOf P L m₀)
    (Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.C.E.curve (Spec.Sha256.bytesAt m (dgArg P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .r3).setWidth 32 = (1 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.C.E.curve rs
  | none => (t.gpr .r3).setWidth 32 = (0 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem
  saved : SavedK P L t.mem (kOf P L t.mem)

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Q_le (P : RfcHash) : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.1

theorem Ctx.dBytes (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) :
    Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega)

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 264, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (r := ⟨L.B + BitVec.ofNat 64 264, 8⟩) (w := 64)
    (by simpa only [Nat.reduceDiv] using Region.contains_self (L.B + BitVec.ofNat 64 264) 8) hd (by decide)

/-- What `core` changes: `out`, `scratch` and the calls' 96 bytes of stack. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B, 96⟩]

/-- The regions the loop writes but the count. -/
def Away {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 96⟩ ∨ r = ⟨L.B, 256⟩ ∨ r = ⟨L.B, 264⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩

/-- The regions the loop writes. -/
def Apart {dn : Nat} (L : Lay dn) (r : Region) : Prop := Away L r ∨ r = ⟨L.B + BitVec.ofNat 64 264, 8⟩

/-- What the loop writes is apart from the frame between `B + 272` and
`B + 544`, where the digest `core` reads is. -/
theorem apart_disj (hL : L.Ok) {r : Region} (h : Apart L r) {d n : Nat} (h₁ : 272 ≤ d) (h₂ : d + n ≤ 544) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact hL.stk_SCR (by omega)
  · exact hL.stk_OUT (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem dgArg_off (P : RfcHash) (L : Lay P.I.hashLen) :
    ∃ d, dgArg P L = L.B + BitVec.ofNat 64 d ∧ 272 ≤ d ∧ d + P.Q ≤ 544 := by
  have := Q_le P
  simp only [dgArg]
  split
  · exact ⟨96 + fXc, rfl, by decide, by simp only [fXc]; omega⟩
  · exact ⟨96 + fX, rfl, by decide, by simp only [fX]; omega⟩

theorem DgOk.frame (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Apart L r) : DgOk P L m₀ m' := by
  have := Q_le P
  obtain ⟨d, hd', h₁, h₂⟩ := dgArg_off P L
  unfold DgOk
  rw [bytesAt_frame hf (fun r hr => by rw [hd']; exact apart_disj hL (hd r hr) h₁ h₂) (by omega)]
  exact h

theorem DgOk.frameA (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Away L r) : DgOk P L m₀ m' := h.frame hL hf fun r hr => .inl (hd r hr)

theorem cnt_away (hL : L.Ok) {ws : List Region} (hd : ∀ r ∈ ws, Away L r) {m m' : Mem} (hf : Frame ws m m') :
    cnt L m' = cnt L m := by
  have := hL.nB
  refine cnt_frame hf fun r hr => ?_
  rcases hd r hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hL.stk_SCR (by omega)
  · exact hL.stk_OUT (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)

theorem kvw_away : ∀ r ∈ KVW L, Away L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [Away]

theorem cw_away : ∀ r ∈ CW L, Away L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [Away]

theorem corew_away : ∀ r ∈ CoreW L, Away L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [Away]

/-- `K` and `V`, kept by memory that changed elsewhere than `[B + 128, B + 256)`. -/
theorem kv_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 256 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    kOf P L m' = kOf P L m ∧ vOf P L m' = vOf P L m := by
  have hD := P.sizes.2.2.2.2.1
  exact ⟨bytesAt_frame hf (fun r hr => hd r hr (d := 128) (n := P.v.H.D) (by omega) (by omega)) (by omega),
    bytesAt_frame hf (fun r hr => hd r hr (d := 192) (n := P.v.H.D) (by omega) (by omega)) (by omega)⟩

theorem corew_kv (hL : L.Ok) : ∀ r ∈ CoreW L, ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 256 →
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) d n h₁ h₂
  · exact hL.stk_OUT (by omega)
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

theorem cntw_kv (hL : L.Ok) : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 264, 8⟩ : Region)], ∀ {d n : Nat}, 128 ≤ d →
    d + n ≤ 256 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [List.mem_singleton]
  rintro r rfl d n h₁ h₂
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

/-- `out`, kept by memory that changed elsewhere. -/
theorem out_keep {ws : List Region} {m m' : Mem} (hL : L.Ok) (hq : L.q = P.Q) (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint L.OUT r) :
    Spec.Sha256.bytesAt m' L.out (2 * P.Q) = Spec.Sha256.bytesAt m L.out (2 * P.Q) :=
  bytesAt_frame hf (fun r hr => by have := hd r hr; simp only [Lay.OUT, hq] at this; exact this)
    (by have := Q_le P; have := hL.no; rw [hq] at this; omega)

theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t)
    (ha : (t'.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## `core` -/

/-- The signature `core` computes from the private key, its digest and `k`. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.C.E.curve (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m L.d P.Q))
    (Spec.Ecdsa.hashToInt P.R.C.E.curve (Spec.Sha256.bytesAt m (dgArg P L) P.Q))
    (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m (kArg P L) P.Q))

theorem kArg_off (P : RfcHash) (L : Lay P.I.hashLen) :
    kArg P L = L.B + BitVec.ofNat 64 (96 + fT) ∧ 128 ≤ 96 + fT ∧ 96 + fT + P.Q ≤ 688 := by
  have := Q_le P; exact ⟨rfl, by decide, by simp only [fT]; omega⟩

/-- `core`'s tables, as its contract asks. -/
theorem core_tables (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t) :
    CoreTables P.R.C.cs t ⟨L.out, 2 * P.R.C.E.curve.len⟩ L.scr := by
  have eQ : P.R.C.E.curve.len = L.q := hq.symm
  have eO : (⟨L.out, 2 * P.R.C.E.curve.len⟩ : Region) = L.OUT := by rw [eQ]
  rw [eO, ← hcs]
  refine ⟨hc.held_now hL, fun T hT => ?_⟩
  rw [hc.tbls] at hT
  obtain ⟨hn, tO, tS, -, al⟩ := hL.tables T hT
  exact ⟨hn, tO, tS, al⟩

/-- The call of `core`: it writes the signature of the private key, its
digest and `k`, or zeros, and changes only `out`, `scratch` and the calls'
stack. -/
theorem core_ok (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t)
    (h3 : t.gpr .r3 = L.out) (h4 : t.gpr .r4 = L.d) (h5 : t.gpr .r5 = dgArg P L) (h6 : t.gpr .r6 = kArg P L)
    (h7 : t.gpr .r7 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g lr m₀ u ∧ Frame (CoreW L) t.mem u.mem ∧
      ResultIs P L (coreSig P L t.mem) u := by
  have hnB := hL.nB
  have hQ := Q_le P
  obtain ⟨dd, hdd, d₁, d₂⟩ := dgArg_off P L
  obtain ⟨hkk, k₁, k₂⟩ := kArg_off P L
  have eQ : P.R.C.E.curve.len = L.q := hq.symm
  have stk : ∀ {d : Nat}, 128 ≤ d → d + P.Q ≤ 688 → (L.B + BitVec.ofNat 64 d).toNat + P.Q ≤ 2 ^ 64 ∧
      Region.Disjoint L.OUT ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ L.SCR ∧
      ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ R := fun h₁ h₂ =>
    ⟨by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]; omega,
      (hL.stk_OUT (by omega)).symm, hL.stk_SCR (by omega), L.FR, by simp, within_fr _ h₁ h₂⟩
  obtain ⟨gn, go, gs, gw⟩ := stk (by omega) (by omega : dd + P.Q ≤ 688)
  obtain ⟨kn, ko, ks, kw⟩ := stk k₁ k₂
  rw [← hdd] at gn go gs gw
  rw [← hkk] at kn ko ks kw
  have eO : (⟨L.out, 2 * P.R.C.E.curve.len⟩ : Region) = L.OUT := by rw [eQ]
  have eD : (⟨L.d, P.R.C.E.curve.len⟩ : Region) = L.D := by rw [eQ]
  refine WP.of_syms (coreCall P.R.C h3 h4 h5 h6 h7 (by rw [eO, eD]; exact hL.od) (by rw [eO]; exact go)
    (by rw [eO]; exact ko) (by rw [eO]; exact hL.oc) (by rw [eD]; exact hL.dc) gs ks
    (by rw [eQ]; exact hL.no) (by rw [eQ]; exact hL.nd) gn kn hL.nc ?_ ?_ ?_ ?_)
  · exact core_tables hL hq hcs hc
  · rw [eO, eD, ← hcs, hc.tbls]
    refine hc.coversT fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | hT) | (rfl | rfl)
    · exact .inl ⟨L.D, by simp, within_base _ (Nat.le_refl _)⟩
    · exact .inl gw
    · exact .inl kw
    · exact .inr hT
    · exact .inl ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact .inl ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
  · rw [eO]
    refine hc.coversW fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
  · intro s' hrd hwr hsp hf hcs hres hsy
    rw [hc.sp, Lay.below96, eO] at hf
    have hf' : Frame (CoreW L) t.mem s'.mem := hf
    refine ⟨hc.keep hL hrd hwr hsp hcs hf' (by
      simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact .inl fun _ h => h
      · exact .inr (.inl fun _ h => h)
      · exact .inr (.inr (.inl (Region.sub_prefix (by omega))))) hsy, hf', ?_⟩
    simp only [Proof.Ecdsa.Rfc6979.ecdsa_bytesAt] at hres
    unfold ResultIs
    exact hres

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i)

/-- `core`'s arguments. -/
structure Args (P : RfcHash) {dn : Nat} (L : Lay dn) (u : State) : Prop where
  r3 : u.gpr .r3 = L.out
  r4 : u.gpr .r4 = L.d
  r5 : u.gpr .r5 = dgArg P L
  r6 : u.gpr .r6 = kArg P L
  r7 : u.gpr .r7 = L.scr

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval (.nonzero .d .r12) u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem try₁_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hq.2.1 hc hi.saved) fun _ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, _⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_away hL cw_away hf₁).trans hi.cnt, hi.fails,
    hi.dg.frameA hL hf₁ cw_away, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u ∧ Args P L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, _, h3, h4, h5, h6, h7⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, h3, h4, h5, h6, h7⟩

/-- `core`'s signature is the candidate's. -/
theorem coreSig_eq (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg P L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  simp only [coreSig, sigI, xOf]
  rw [hc.dBytes hL hq, hkv]
  exact congrArg (fun e => Spec.Ecdsa.signWith _ _ e _) hdg

theorem try₃_ok (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : Args P L t) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g lr m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok hL hq hcs hc ha.r3 ha.r4 ha.r5 ha.r6 ha.r7) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hq hc hi.dg hi.kk] at hr₃
  obtain ⟨ek, ev⟩ := kv_keep (P := P) hf₃ (corew_kv hL)
  exact ⟨hc₃, hi.lt, ek.trans hi.k, ev.trans hi.v, (cnt_away hL corew_away hf₃).trans hi.cnt, hi.fails,
    hi.dg.frameA hL hf₃ corew_away, hr₃⟩

theorem and_one_of {x : BitVec 64} {b : BitVec 32} (h : x.setWidth 32 = b) (hb : b.toNat ≤ 1) :
    x &&& 1 = BitVec.ofNat 64 b.toNat :=
  BitVec.eq_of_toNat_eq (by
    have e := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth] at e
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega)

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 64 (T - i) - 1 = BitVec.ofNat 64 (T - (i + 1)) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega)

theorem try₄_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g lr m₀ u ∧ Mid P L m₀ i u := by
  have hT := P.tries_lt
  refine WP.mono (goOn_ok hL hc) fun u ⟨hcu, K, hf, hcnt, h12⟩ => ?_
  obtain ⟨ek, ev⟩ := kv_keep (P := P) hf (cntw_kv hL)
  have hc3 : (u.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32 := by rw [K.gpr _ (by decide)]
  have hout := out_keep (P := P) hL hq hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega)).symm)
  refine ⟨hcu, hi.lt, ek.trans hi.k, ev.trans hi.v, by rw [hcnt, hi.cnt, cnt_sub hi.lt], hi.fails,
    hi.dg.frame hL hf (fun r hr => by simp only [List.mem_singleton] at hr; exact .inr hr),
    hi.res.keep hc3 hout, ?_⟩
  rw [eval_nonzero, h12, hi.cnt, cnt_sub hi.lt]
  have hres := hi.res
  unfold ResultIs at hres
  cases hs : sigI P L m₀ i <;> rw [hs] at hres
  · rw [and_one_of hres.1 (by decide)]
    have : (BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 &&& BitVec.ofNat 64 (P.I.tries - (i + 1))) =
        BitVec.ofNat 64 (P.I.tries - (i + 1)) := by
      rw [show BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
    rw [this, bne, ofNat_beq_zero (by omega)]
    simp only [true_and, Option.some.injEq]
    rw [← decide_not]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · rw [and_one_of hres.1 (by decide)]
    simp

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : Mid P L m₀ i t) :
    WP isa (.ite (.nonzero .d .r12) (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' =>
      Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL hq hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅, hS₅⟩ => ?_)
    refine again_ok fun u₆ k₆ m₆ v₆ s₆ => ⟨hc₅.kp hL k₆ m₆ s₆, .inr ⟨by rw [eval_nonzero, v₆]; rfl, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.v.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_, by rw [m₆]; exact hS₅⟩
    · rw [m₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [m₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [m₆, cnt_away hL kvw_away hf₅, hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [m₆]; exact hi.dg.frameA hL hf₅ kvw_away
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine stop_ok fun u₅ k₅ m₅ v₅ s₅ => ⟨hc.kp hL k₅ m₅ s₅, .inl ⟨by rw [eval_nonzero, v₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep (by rw [k₅.gpr _ (by decide)]) (by rw [m₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hq hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hq.1 hq.2.2 h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hq.1 h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hq h₄ p₄))))

theorem tries_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .d .r12)) t fun t' => Ctx L g lr m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g lr m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧
    n ≤ P.I.tries) ?_ P.I.tries t ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hq hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
