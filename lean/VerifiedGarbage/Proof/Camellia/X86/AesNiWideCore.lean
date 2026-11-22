module

public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideMaps
public import VerifiedGarbage.Proof.Camellia.X86.AesNiCore
public import VerifiedGarbage.Proof.Camellia.X86.ModeCore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher

/-!
# Camellia's four blocks by the AES S-box on x86 (32-bit): the core of the modes

`coreSpec d`: `Impl.Camellia.X86.AesNiWide.core d` meets what the modes
need of a core (`Proof.Modes.X86.CoreSpec`), with the key the number of
rounds and the schedule's words, read through the first two stack
arguments, and its cipher `Spec.Camellia.cipher` or, for decryption,
`Spec.Camellia.invCipher` under them.

* The steps of the parts one pair after the other
  (`Proof/Camellia/X86/AesNiWideMaps.lean`), as statements about the
  registers' bytes, each of a quadword what `AesNiCore.lean` says of a
  register's two (`round_wp`, `rounds6_wp`, …), with that file's maps and
  Camellia's F.
* Those parts on the places of the scratch buffer (`refGroup_wp`, …), and
  from them the parts as they run (`group_wp`, …, by
  `SseEquiv.equiv_wp`), and `crypt_wp`: the four blocks of the modes'
  buffer, each enciphered under the keys in the scratch buffer
  (`AesNi.Keys`).
* `prepare_wp`: the copy of the schedule holds its subkeys in `d`'s order
  (what each of its blocks stores is checked by the kernel, `copy_all`),
  and the rest is `AesNi.prepare`'s loop, whose statements are of the 544
  bytes of scratch buffer that code knows and here hold in the larger one
  (`WP.narrow`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiWide

/-! ## What the steps compute -/

section

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNiWide
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 oN oT oI x ld stx)
open VG.Proof.Camellia.X86.AesNi (qT qI isA slot kind sets kOf glin dq gc c5 bswq kb bz nmap regs₀ var cterms maskOk
  tblAt slot_lt slot_slot glin_congr glin_f dq_xor)

/-- What every step needs of the state: the table's address in its
register, the 136 bytes of keys at `esi` readable, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr kr).toNat + 136 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 136 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

theorem Env.rel {s : State} (h : Env s) : Rel wparams (envOf wparams s) regs₀ s :=
  (rel_init (p := wparams) h.tb h.fit h.acc).const m0 h.msk

/-- The input bytes are `AesNi`'s. -/
theorem wenv (s : State) : envOf wparams s = envOf AesNi.params s := rfl

section
variable {s : State}

theorem Env.same {s' : State} (he : Env s) (hs : Same s s') (hm : ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) :
    Env s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨he.tb, he.fit, he.acc, hm⟩

/-- The terms of `roundRef`, for any list of bytes. -/
theorem sum_terms (env : Nat → BitVec 8) (v : Nat → Nat) (a : Bool) (l : List Nat) :
    sum env (l.flatMap fun i =>
      [⟨[.look (tblAt (oN (kOf a (kind i)))), .xorc 0x0f#8, .and 0x0f#8, .aes], v i⟩,
       ⟨[.look (tblAt (oN (kOf a (kind i)) + 16)), .hi4, .aes], v i⟩]) =
      l.foldr (fun i acc => nmap (kOf a (kind i)) (aesSbox (mask env (v i) nvars)) ^^^ acc) 0#8 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, sum, List.foldr_cons, ih]
    rw [← BitVec.xor_assoc]; rfl

theorem env_var_slot (r : XReg) {q : Nat} (hq : q < 16) (j : Nat) :
    mask (envOf AesNi.params s) (var r (8 * (q / 8) + slot j)) nvars = byte (s.xmm r) (8 * (q / 8) + slot j) :=
  AesNi.env_var r (by have := slot_lt j; omega_arith)

/-- Round `i` of a group: `xr` takes its eight key bytes in both quadwords
(but in the last round), and each quadword of `y` the round's map of the
S-boxes of that quadword of `xr`. -/
theorem round_wp {xr y : XReg} {i : Nat} (hok : roundOk xr y i = true) (he : Env s) :
    WP isa (.block (round xr y i)) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm xr) q =
        byte (s.xmm xr) q ^^^ (if i < 5 then kb s (16 + 8 * i + q % 8) else 0#8)) ∧
      (∀ q < 16, byte (s'.xmm y) q = byte (s.xmm y) q ^^^
        glin (fun j => aesSbox (byte (s.xmm xr) (8 * (q / 8) + slot j))) (slot (q % 8))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hx, hy⟩, cy⟩, cx⟩, hm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, fun q hq => ?_, AesNi.rel_mask hr hm⟩
  · rw [AesNi.rel_bytes hr hx cx hq, wenv]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, AesNi.env_var xr hq]
    by_cases h5 : i < 5
    · rw [ite_eq_left h5, ite_eq_left h5, show 128 + 16 + 8 * i + q % 8 = 128 + (16 + 8 * i + q % 8) by omega_arith,
        AesNi.env_key (by omega_arith)]
    · rw [ite_eq_right h5, ite_eq_right h5, mask_zero]
  · rw [AesNi.rel_bytes hr hy cy hq, wenv, roundRef, BV.eval, sum_terms, AesNi.env_var y hq, BitVec.xor_zero, glin]
    simp only [env_var_slot xr hq]

/-- The register `x` holds the bytes `F L` of a half in its quadword `L`:
byte `j` in slot `slot j` of the quadword. -/
def Lanes (x : BitVec 128) (F : Nat → Nat → Byte) : Prop := ∀ L < 2, ∀ j < 8, byte x (8 * L + slot j) = F L j

theorem Lanes.congr {x : BitVec 128} {F G : Nat → Nat → Byte} (h : Lanes x F)
    (e : ∀ L < 2, ∀ j < 8, F L j = G L j) : Lanes x G :=
  fun L hL j hj => (h L hL j hj).trans (e L hL j hj)

theorem lane_idx {L j : Nat} (hL : L < 2) :
    8 * L + slot j < 16 ∧ (8 * L + slot j) % 8 = slot j ∧ (8 * L + slot j) / 8 = L := by
  have := slot_lt j
  omega_arith

/-- `round_wp`, of the quadwords. -/
theorem round_lanes {xr y : XReg} {i : Nat} (hok : roundOk xr y i = true) (he : Env s)
    {F G : Nat → Nat → Byte} (hx : Lanes (s.xmm xr) F) (hy : Lanes (s.xmm y) G) :
    WP isa (.block (round xr y i)) s fun s' => Same s s' ∧ Env s' ∧
      Lanes (s'.xmm xr) (fun L j => F L j ^^^ (if i < 5 then kb s (16 + 8 * i + slot j) else 0#8)) ∧
      Lanes (s'.xmm y) (fun L j => G L j ^^^ glin (fun i => aesSbox (F L i)) j) := by
  refine WP.mono (round_wp hok he) fun s' ⟨hs, hX, hY, hm⟩ =>
    ⟨hs, he.same hs hm, fun L hL j hj => ?_, fun L hL j hj => ?_⟩
  · obtain ⟨h16, h8, _⟩ := lane_idx (j := j) hL
    rw [hX _ h16, h8, hx L hL j hj]
  · obtain ⟨h16, h8, hd⟩ := lane_idx (j := j) hL
    rw [hY _ h16, h8, hd, hy L hL j hj, slot_slot hj]
    exact congrArg (G L j ^^^ ·) (glin_congr (fun i hi => congrArg aesSbox (hx L hL i hi)) hj)

theorem ok0 (i : Nat) (hi : i ∈ [0, 2, 4]) : roundOk .xmm0 .xmm1 i = true := List.all_eq_true.mp round_all.1 i hi
theorem ok1 (i : Nat) (hi : i ∈ [1, 3, 5]) : roundOk .xmm1 .xmm0 i = true := List.all_eq_true.mp round_all.2 i hi

theorem kb_same {s' : State} (hs : Same s s') (o : Nat) : kb s' o = kb s o := by
  obtain ⟨f, rfl⟩ := hs; rfl

open VG.Proof.Camellia (pair)

/-- Two rounds, whose keys' differences are with `kc` and `kd`. -/
theorem pair_wp {i : Nat} (hi : i = 0 ∨ i = 2) (he : Env s) {ka kb' kc kd : BitVec 64} {a b : Nat → BitVec 64}
    (h₁ : ∀ j < 8, kb s (16 + 8 * i + slot j) = dq (ka ^^^ kc) j ^^^ gc j)
    (h₂ : ∀ j < 8, kb s (16 + 8 * (i + 1) + slot j) = dq (kb' ^^^ kd) j ^^^ gc j)
    (h0 : Lanes (s.xmm .xmm0) fun L j => dq (a L) j ^^^ dq ka j ^^^ c5)
    (h1 : Lanes (s.xmm .xmm1) fun L j => dq (b L) j ^^^ dq kb' j ^^^ c5 ^^^ gc j) :
    WP isa (.block (round .xmm0 .xmm1 i ++ round .xmm1 .xmm0 (i + 1))) s fun s' => Same s s' ∧ Env s' ∧
      Lanes (s'.xmm .xmm0) (fun L j => dq (pair ka kb' (a L, b L)).1 j ^^^ dq kc j ^^^ c5) ∧
      Lanes (s'.xmm .xmm1) (fun L j => dq (pair ka kb' (a L, b L)).2 j ^^^ dq kd j ^^^ c5 ^^^ gc j) := by
  have o0 : roundOk .xmm0 .xmm1 i = true := ok0 i (by rcases hi with rfl | rfl <;> decide)
  have o1 : roundOk .xmm1 .xmm0 (i + 1) = true := ok1 (i + 1) (by rcases hi with rfl | rfl <;> decide)
  have i5 : i < 5 := by omega_arith
  have i5' : i + 1 < 5 := by omega_arith
  refine WP.block_append_iff.mpr (WP.mono (round_lanes o0 he h0 h1) fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have x₁ := x₁.congr (G := fun L j => dq (a L) j ^^^ dq kc j ^^^ c5 ^^^ gc j) fun L _ j hj =>
    (congrArg (dq (a L) j ^^^ dq ka j ^^^ c5 ^^^ ·) ((ite_eq_left i5).trans (h₁ j hj))).trans (AesNi.tgt (a L) ka kc j)
  have y₁ := y₁.congr (G := fun L j => dq (b L ^^^ Spec.Camellia.f (a L) ka) j ^^^ dq kb' j ^^^ c5)
    fun L _ j hj => AesNi.src (a L) (b L) ka kb' hj
  refine WP.mono (round_lanes o1 he₁ y₁ x₁) fun s₂ ⟨e₂, he₂, y₂, x₂⟩ => ?_
  refine ⟨e₁.trans e₂, he₂, x₂.congr fun L _ j hj => AesNi.src _ (a L) kb' kc hj, y₂.congr fun L _ j hj => ?_⟩
  have hk : kb s₁ (16 + 8 * (i + 1) + slot j) = dq (kb' ^^^ kd) j ^^^ gc j := (kb_same e₁ _).trans (h₂ j hj)
  exact (congrArg (dq (b L ^^^ Spec.Camellia.f (a L) ka) j ^^^ dq kb' j ^^^ c5 ^^^ ·)
    ((ite_eq_left i5').trans hk)).trans (AesNi.tgt _ kb' kd j)

/-- The last two rounds of a group: the second half is left with the last
round's key. -/
theorem lastpair_wp (he : Env s) {ka kb' : BitVec 64} {a b : Nat → BitVec 64}
    (h₁ : ∀ j < 8, kb s (48 + slot j) = dq ka j ^^^ gc j ^^^ c5)
    (h0 : Lanes (s.xmm .xmm0) fun L j => dq (a L) j ^^^ dq ka j ^^^ c5)
    (h1 : Lanes (s.xmm .xmm1) fun L j => dq (b L) j ^^^ dq kb' j ^^^ c5 ^^^ gc j) :
    WP isa (.block (round .xmm0 .xmm1 4 ++ round .xmm1 .xmm0 5)) s fun s' => Same s s' ∧ Env s' ∧
      Lanes (s'.xmm .xmm0) (fun L => dq (pair ka kb' (a L, b L)).1) ∧
      Lanes (s'.xmm .xmm1) (fun L j => dq (pair ka kb' (a L, b L)).2 j ^^^ dq kb' j ^^^ c5) := by
  refine WP.block_append_iff.mpr (WP.mono (round_lanes (ok0 4 (by decide)) he h0 h1)
    fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have x₁ := x₁.congr (G := fun L j => dq (a L) j ^^^ gc j) fun L _ j hj =>
    (congrArg (dq (a L) j ^^^ dq ka j ^^^ c5 ^^^ ·) ((ite_eq_left (by decide)).trans (h₁ j hj))).trans
      (AesNi.tgt4 (a L) ka j)
  have y₁ := y₁.congr (G := fun L j => dq (b L ^^^ Spec.Camellia.f (a L) ka) j ^^^ dq kb' j ^^^ c5)
    fun L _ j hj => AesNi.src (a L) (b L) ka kb' hj
  refine WP.mono (round_lanes (ok1 5 (by decide)) he₁ y₁ x₁) fun s₂ ⟨e₂, he₂, y₂, x₂⟩ => ?_
  refine ⟨e₁.trans e₂, he₂, x₂.congr fun L _ j hj => AesNi.src5 _ (a L) kb' hj, y₂.congr fun L _ j _ => ?_⟩
  rw [ite_eq_right (by decide), BitVec.xor_zero]
  rfl

/-- The six rounds of a group: from the halves `a L` and `b L` with the
first two keys, in the quadwords of `xmm0` and `xmm1`, to the halves after
the three pairs of rounds, the second with the last round's key. -/
theorem rounds6_wp (he : Env s) {k : Nat → BitVec 64} (hk : AesNi.GroupKeys s k) {a b : Nat → BitVec 64}
    (h0 : Lanes (s.xmm .xmm0) fun L j => dq (a L) j ^^^ dq (k 0) j ^^^ c5)
    (h1 : Lanes (s.xmm .xmm1) fun L j => dq (b L) j ^^^ dq (k 1) j ^^^ c5 ^^^ gc j) :
    WP isa (.block rounds6) s fun s' => Same s s' ∧ Env s' ∧
      Lanes (s'.xmm .xmm0) (fun L =>
        dq (pair (k 4) (k 5) (pair (k 2) (k 3) (pair (k 0) (k 1) (a L, b L)))).1) ∧
      Lanes (s'.xmm .xmm1) (fun L j =>
        dq (pair (k 4) (k 5) (pair (k 2) (k 3) (pair (k 0) (k 1) (a L, b L)))).2 j ^^^ dq (k 5) j ^^^ c5) := by
  unfold rounds6
  rw [← List.append_assoc, ← List.append_assoc (round .xmm0 .xmm1 2)]
  refine WP.block_append_iff.mpr (WP.mono (pair_wp (.inl rfl) he (hk.d 0 (by decide)) (hk.d 1 (by decide)) h0 h1)
    fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have k₁ := hk.same e₁
  refine WP.block_append_iff.mpr (WP.mono (pair_wp (.inr rfl) he₁ (k₁.d 2 (by decide)) (k₁.d 3 (by decide)) x₁ y₁)
    fun s₂ ⟨e₂, he₂, x₂, y₂⟩ => ?_)
  have k₂ := k₁.same e₂
  exact WP.mono (lastpair_wp he₂ k₂.d4 x₂ y₂) fun s₃ ⟨e₃, he₃, x₃, y₃⟩ => ⟨(e₁.trans e₂).trans e₃, he₃, x₃, y₃⟩

/-! ### The conversions -/

/-- The two blocks in `xmm0` and `xmm1`, each in the order of `BSW`, to the
rounds' form with the first keys: their first halves in the quadwords of
`xmm3`, their second in those of `xmm1`. -/
theorem inX_wp (he : Env s) :
    WP isa (.block inX) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm .xmm3) q =
        qT (isA (slot (q % 8))) (byte (s.xmm (xreg (q / 8))) (bswq (q % 8))) ^^^ kb s (q % 8)) ∧
      (∀ q < 16, byte (s'.xmm .xmm1) q =
        qT (isA (slot (q % 8))) (byte (s.xmm (xreg (q / 8))) (bswq (q % 8 + 8))) ^^^ kb s (8 + q % 8)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := conv_all.1
  unfold inOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨h3, h1⟩, c3⟩, c1⟩, hm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, fun q hq => ?_, AesNi.rel_mask hr hm⟩
  · rw [AesNi.rel_bytes hr h3 c3 hq, wenv]
    simp only [BV.eval, BitVec.xor_zero, AesNi.cterms_eval _ (.inl rfl) hq, blockVar]
    rw [AesNi.env_var _ (AesNi.bswq_lt (show q % 8 < 16 by omega_arith)), AesNi.env_key (by omega_arith)]
    exact BitVec.xor_comm _ _
  · rw [AesNi.rel_bytes hr h1 c1 hq, wenv]
    simp only [BV.eval, BitVec.xor_zero, AesNi.cterms_eval _ (.inl rfl) hq, blockVar]
    rw [AesNi.env_var _ (AesNi.bswq_lt (show q % 8 + 8 < 16 by omega_arith)), AesNi.env_key (by omega_arith)]
    exact BitVec.xor_comm _ _

/-- The half in `xmm0` (the second with the last round's keys still to
take), out of the rounds' form, as the bytes of `xmm3`. -/
theorem halfIn_wp {h : Nat} (hh : h = 0 ∨ h = 1) (he : Env s) :
    WP isa (.block (halfIn h)) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm .xmm3) q =
        qI (isA (slot (q % 8))) (byte (s.xmm .xmm0) q ^^^ (if h = 1 then kb s (56 + q % 8) else 0#8))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok : halfInOk h = true := by
    rcases hh with rfl | rfl
    · exact conv_all.2.1
    · exact conv_all.2.2.1
  unfold halfInOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨h3, c3⟩, hm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, AesNi.rel_mask hr hm⟩
  rw [AesNi.rel_bytes hr h3 c3 hq, wenv]
  simp only [BV.eval, BitVec.xor_zero, BitVec.zero_xor, mask_zero, AesNi.cterms_eval _ (.inr rfl) hq, mask_xor,
    AesNi.env_var .xmm0 hq]
  rcases hh with rfl | rfl
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), mask_zero]; rfl
  · rw [ite_eq_left rfl, ite_eq_left rfl, AesNi.env_key (by omega_arith)]; rfl

/-- The bytes of `xmm3`, into the rounds' form with the next group's first
keys, in `xmm1`. -/
theorem halfOut_wp {h : Nat} (hh : h = 0 ∨ h = 1) (he : Env s) :
    WP isa (.block (halfOut h)) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm .xmm1) q =
        qT (isA (slot (q % 8))) (byte (s.xmm .xmm3) q) ^^^ kb s (112 + 8 * h + q % 8)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok : halfOutOk h = true := by
    rcases hh with rfl | rfl
    · exact conv_all.2.2.2.1
    · exact conv_all.2.2.2.2.1
  unfold halfOutOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨h1, c1⟩, hm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, AesNi.rel_mask hr hm⟩
  rw [AesNi.rel_bytes hr h1 c1 hq, wenv]
  simp only [BV.eval, BitVec.xor_zero, AesNi.cterms_eval _ (.inl rfl) hq, AesNi.env_var .xmm3 hq]
  rw [AesNi.env_key (by omega_arith)]
  exact BitVec.xor_comm _ _

/-- The halves in `xmm0` and `xmm1` after the last round (the second with
its keys still to take), as the bytes of block `L` of the pair, in `xmm0`
or `xmm2`, with the last keys (at byte 64). -/
theorem join_wp (he : Env s) :
    WP isa (.block joinX) s fun s' => Same s s' ∧
      ∀ L < 2, ∀ q < 16, byte (s'.xmm (if L = 0 then .xmm0 else .xmm2)) q =
        qI (isA (slot (bswq q % 8)))
          (if bswq q < 8 then byte (s.xmm .xmm1) (8 * L + bswq q) ^^^ kb s (56 + bswq q)
            else byte (s.xmm .xmm0) (8 * L + (bswq q - 8))) ^^^ kb s (64 + q) := by
  have hok := conv_all.2.2.2.2.2
  unfold joinOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨h0, h2⟩, c0⟩, c2⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun L hL q hq => ?_⟩
  have hb := AesNi.bswq_lt hq
  have key : ∀ (r : XReg) (hsh : (ρ.get r).sh = false)
      (hc : ((List.range 16).all fun q => (get (ρ.get r).bs q).same (joinRef L q)) = true),
      byte (s'.xmm r) q = qI (isA (slot (bswq q % 8)))
          (if bswq q < 8 then byte (s.xmm .xmm1) (8 * L + bswq q) ^^^ kb s (56 + bswq q)
            else byte (s.xmm .xmm0) (8 * L + (bswq q - 8))) ^^^ kb s (64 + q) := fun r hsh hc => by
    rw [AesNi.rel_bytes hr hsh hc hq, wenv, joinRef]
    by_cases h8 : bswq q < 8
    · simp only [ite_eq_left h8, BV.eval, BitVec.xor_zero, AesNi.cterms_eval _ (.inr rfl) hb, mask_xor]
      rw [AesNi.env_var _ (by omega_arith), AesNi.env_key (by omega_arith), AesNi.env_key (by omega_arith)]
      exact BitVec.xor_comm _ _
    · simp only [ite_eq_right h8, BV.eval, BitVec.xor_zero, AesNi.cterms_eval _ (.inr rfl) hb]
      rw [AesNi.env_var _ (by omega_arith), AesNi.env_key (by omega_arith)]
      exact BitVec.xor_comm _ _
  have hL' : L = 0 ∨ L = 1 := by omega_arith
  rcases hL' with rfl | rfl
  · exact key .xmm0 h0 c0
  · exact key .xmm2 h2 c2

/-! ### The FL layer -/

/-- A quadword, in both quadwords of a register: `movq` and `punpcklqdq`. -/
def dupq (w : BitVec 64) : BitVec 128 :=
  XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ w) ((0 : BitVec 64) ++ w)

theorem getLsbD_qword_zext (w : BitVec 64) {j : Nat} (h : j < 64) :
    (qword ((0 : BitVec 64) ++ w) 0).getLsbD j = w.getLsbD j := by
  simp only [qword, BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add, h, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append, ite_eq_left h]

theorem getLsbD_dupq (w : BitVec 64) {j : Nat} (hj : j < 128) : (dupq w).getLsbD j = w.getLsbD (j % 64) := by
  show (qword _ 0 ++ qword _ 0).getLsbD j = _
  rw [BitVec.getLsbD_append]
  by_cases h : j < 64
  · rw [ite_eq_left h, getLsbD_qword_zext _ h, Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h, getLsbD_qword_zext _ (by omega_using [hj, h]), show j % 64 = j - 64 by omega_using [hj, h]]

theorem dword_dupq (w : BitVec 64) {k : Nat} (hk : k < 4) :
    dword (dupq w) k = w.extractLsb' (32 * (k % 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_dupq _ (by omega_arith)]
  exact congrArg _ (by omega_arith)

theorem extract_readW64 (m : Mem) (a : Addr) {c : Nat} (hc : c < 2) :
    (m.readW a 64).extractLsb' (32 * c) 32 = m.readW (a + BitVec.ofNat 64 (4 * c)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega_arith), getLsbD_read _ _ (by omega_arith)]
  rw [show a + BitVec.ofNat 64 ((32 * c + i) / 8) = a + BitVec.ofNat 64 (4 * c) + BitVec.ofNat 64 (i / 8) by
    rw [show (32 * c + i) / 8 = 4 * c + i / 8 by omega_arith, BitVec.ofNat_add, BitVec.add_assoc]]
  rw [decide_eq_true (by omega_arith), Bool.true_and]; exact congrArg _ (by omega_arith)

/-- The doublewords of a quadword of the keys, in both quadwords, are those
of the 16 bytes it is a quadword of. -/
theorem dword_dupq_readW (m : Mem) (a : Addr) {h : Nat} (hh : h < 2) {x c : Nat} (hx : x < 2) (hc : c < 2) :
    dword (dupq (m.readW (a + BitVec.ofNat 64 (8 * h)) 64)) (2 * x + c) = dword (m.readW a 128) (2 * h + c) := by
  rw [dword_dupq _ (by omega_arith), show (2 * x + c) % 2 = c by omega_arith, extract_readW64 _ _ hc,
    dword_readW _ _ (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * h + 4 * c = 4 * (2 * h + c) by omega_arith]

/-- `AesNi.flv` acts on each quadword by itself, and alike on both. -/
theorem flv_lane {v v' e e' : BitVec 128} {a b : Nat} (ha : a < 2) (hb : b < 2)
    (hv : ∀ c < 2, dword v (2 * a + c) = dword v' (2 * b + c))
    (he : ∀ c < 2, dword e (2 * a + c) = dword e' (2 * b + c)) :
    ∀ c < 2, dword (AesNi.flv v e) (2 * a + c) = dword (AesNi.flv v' e') (2 * b + c) := by
  intro c hc
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have e0 := he 0 (by decide)
  have e1 := he 1 (by decide)
  simp only [Nat.add_zero] at v0 e0
  rw [AesNi.dword_flv _ _ (by omega_arith), AesNi.dword_flv _ _ (by omega_arith)]
  have hc' : c = 0 ∨ c = 1 := by omega_arith
  rcases hc' with rfl | rfl
  · rw [ite_eq_left (by omega_arith), ite_eq_left (by omega_arith)]
    simp only [Nat.add_zero]
    rw [v0, e1, v1]
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), Nat.add_sub_cancel, Nat.add_sub_cancel,
      v1, e0, v0]

/-- The FL layer's three steps: two of `AesNi.flv`, the constants between. -/
def fl3 (v e1 c e2 : BitVec 128) : BitVec 128 := AesNi.flv (XBinOp.eval .pxor (AesNi.flv v e1) c) e2

theorem fl3_lane {v v' e1 e1' k k' e2 e2' : BitVec 128} {a b : Nat} (ha : a < 2) (hb : b < 2)
    (hv : ∀ c < 2, dword v (2 * a + c) = dword v' (2 * b + c))
    (h1 : ∀ c < 2, dword e1 (2 * a + c) = dword e1' (2 * b + c))
    (hk : ∀ c < 2, dword k (2 * a + c) = dword k' (2 * b + c))
    (h2 : ∀ c < 2, dword e2 (2 * a + c) = dword e2' (2 * b + c)) :
    ∀ c < 2, dword (fl3 v e1 k e2) (2 * a + c) = dword (fl3 v' e1' k' e2') (2 * b + c) :=
  flv_lane ha hb (fun c hc => by rw [dword_pxor, dword_pxor, flv_lane ha hb hv h1 c hc, hk c hc]) h2

open AesNi (hl LayerWords) in
/-- FL of both quadwords (`h = 0`, the masks the first quadwords of the
layer's) or FL⁻¹ (`h = 1`, the second). -/
theorem fl3_half {h : Nat} (hh : h = 0 ∨ h = 1) {m1 mc m2 : BitVec 128} {w : Nat → BitVec 128} {ke1 ke2 : BitVec 64}
    (hw : LayerWords w ke1 ke2) (A0 A1 : BitVec 64)
    (h1 : ∀ a < 2, ∀ c < 2, dword m1 (2 * a + c) = dword (w 64) (2 * h + c))
    (hc : ∀ a < 2, ∀ c < 2, dword mc (2 * a + c) = dword (w 96) (2 * h + c))
    (h2 : ∀ a < 2, ∀ c < 2, dword m2 (2 * a + c) = dword (w 80) (2 * h + c)) :
    fl3 (hl A0 A1) m1 mc m2 =
      if h = 0 then hl (Spec.Camellia.fl A0 ke1) (Spec.Camellia.fl A1 ke1)
      else hl (Spec.Camellia.flinv A0 ke2) (Spec.Camellia.flinv A1 ke2) := by
  have key : ∀ (L R : BitVec 64), fl3 (hl L R) (w 64) (w 96) (w 80) =
      hl (Spec.Camellia.fl L ke1) (Spec.Camellia.flinv R ke2) := fun L R => by
    rw [fl3, hw.e1, hw.c, hw.e2, AesNi.flv_fl]
  rcases hh with rfl | rfl
  · rw [ite_eq_left rfl]
    have g0 := fl3_lane (a := 0) (b := 0) (v := hl A0 A1) (v' := hl A0 0) (by decide) (by decide)
      (fun c hc => by have : c = 0 ∨ c = 1 := by omega_arith
                      rcases this with rfl | rfl <;> simp [hl]) (h1 0 (by decide)) (hc 0 (by decide)) (h2 0 (by decide))
    have g1 := fl3_lane (a := 1) (b := 0) (v := hl A0 A1) (v' := hl A1 0) (by decide) (by decide)
      (fun c hc => by have : c = 0 ∨ c = 1 := by omega_arith
                      rcases this with rfl | rfl <;> simp [hl]) (h1 1 (by decide)) (hc 1 (by decide)) (h2 1 (by decide))
    rw [key] at g0 g1
    refine ext_dword ?_ ?_ ?_ ?_
    · exact (g0 0 (by decide)).trans (by simp [hl])
    · exact (g0 1 (by decide)).trans (by simp [hl])
    · exact (g1 0 (by decide)).trans (by simp [hl])
    · exact (g1 1 (by decide)).trans (by simp [hl])
  · rw [ite_eq_right (by decide)]
    have g0 := fl3_lane (a := 0) (b := 1) (v := hl A0 A1) (v' := hl 0 A0) (by decide) (by decide)
      (fun c hc => by have : c = 0 ∨ c = 1 := by omega_arith
                      rcases this with rfl | rfl <;> simp [hl]) (h1 0 (by decide)) (hc 0 (by decide)) (h2 0 (by decide))
    have g1 := fl3_lane (a := 1) (b := 1) (v := hl A0 A1) (v' := hl 0 A1) (by decide) (by decide)
      (fun c hc => by have : c = 0 ∨ c = 1 := by omega_arith
                      rcases this with rfl | rfl <;> simp [hl]) (h1 1 (by decide)) (hc 1 (by decide)) (h2 1 (by decide))
    rw [key] at g0 g1
    refine ext_dword ?_ ?_ ?_ ?_
    · exact (g0 0 (by decide)).trans (by simp [hl])
    · exact (g0 1 (by decide)).trans (by simp [hl])
    · exact (g1 0 (by decide)).trans (by simp [hl])
    · exact (g1 1 (by decide)).trans (by simp [hl])

/-- The quadword at `off` of the keys, in both quadwords of a register. -/
def kq (s : State) (off : Nat) : BitVec 128 := dupq (s.mem.readW (addr (s.gpr kr) off) 64)

theorem step_wp {off : Nat} (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr kr) off) 16) :
    WP isa (.block (step .xmm3 .xmm0 .xmm1 .xmm2 off)) s fun s' => Same s s' ∧
      s'.xmm .xmm3 = AesNi.flv (s.xmm .xmm3) (kq s off) ∧ s'.xmm m0 = s.xmm m0 := by
  refine Wp.cons (s' := { s with xmm := fun r =>
      if r = .xmm0 then (0 : BitVec 64) ++ s.mem.readW (addr (s.gpr kr) off) 64 else s.xmm r }) ?_
    (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl
      (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl (AesNi.wp_xs rfl
        (WP.block_nil ⟨⟨_, rfl⟩, rfl, rfl⟩))))))))))))
  show (s.load64 (addr (s.gpr kr) off)).map _ = _
  rw [State.load64, ite_eq_left (contains_8 ha)]; rfl

/-- FL (`h = 0`) or FL⁻¹ (`h = 1`) of both quadwords of `xmm3`: the three
steps, with the quadwords `h` of the layer's masks. -/
theorem halfMid_wp {h : Nat} (hh : h = 0 ∨ h = 1) (he : Env s) :
    WP isa (.block (halfMid h)) s fun s' => Same s s' ∧ Env s' ∧
      s'.xmm .xmm3 = fl3 (s.xmm .xmm3) (kq s (64 + 8 * h)) (kq s (96 + 8 * h)) (kq s (80 + 8 * h)) := by
  have a64 := he.acc (64 + 8 * h) (by omega_arith)
  have a96 := he.acc (96 + 8 * h) (by omega_arith)
  have a80 := he.acc (80 + 8 * h) (by omega_arith)
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (step_wp a64) fun s₁ ⟨e₁, v₁, m₁⟩ => ?_))
  obtain ⟨f₁, rfl⟩ := e₁
  refine Wp.cons (s' := { s with xmm := fun r =>
      if r = .xmm0 then (0 : BitVec 64) ++ s.mem.readW (addr (s.gpr kr) (96 + 8 * h)) 64 else f₁ r }) ?_
    (AesNi.wp_xs rfl (AesNi.wp_xs rfl (WP.block_nil ?_)))
  · show (State.load64 _ (addr (s.gpr kr) (96 + 8 * h))).map _ = _
    rw [State.load64, ite_eq_left (contains_8 a96)]; rfl
  refine WP.mono (step_wp a80) fun s₃ ⟨e₃, v₃, m₃⟩ => ?_
  obtain ⟨f₃, rfl⟩ := e₃
  refine ⟨⟨_, rfl⟩, ⟨he.tb, he.fit, he.acc, fun q hq => ?_⟩, ?_⟩
  · show byte (f₃ m0) q = _
    rw [show f₃ m0 = f₁ m0 from m₃, show f₁ m0 = s.xmm m0 from m₁]; exact he.msk q hq
  · show f₃ .xmm3 = _
    rw [show f₃ .xmm3 = AesNi.flv (XBinOp.eval .pxor (f₁ .xmm3) (kq s (96 + 8 * h))) (kq s (80 + 8 * h)) from v₃,
      show f₁ .xmm3 = AesNi.flv (s.xmm .xmm3) (kq s (64 + 8 * h)) from v₁]
    rfl

end

end

/-! ## The parts on the scratch buffer -/

section

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNiWide
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 x ld stx)
open VG.Impl.Modes.X86 (sb at_ argOp)
open VG.Proof.Modes.X86 (ScrIn)
open VG.Proof.Camellia.X86.AesNi (qT qI isA slot dq gc c5 bswq kb bz slot_lt slot_slot dq_xor kAt wAt Keys)

/-- The 16 bytes at byte `o` of the scratch buffer at `B`. -/
def pw (m : Mem) (B : BitVec 32) (o : Nat) : BitVec 128 := m.readW (B.setWidth 64 + BitVec.ofNat 64 o) 128

theorem byte_pw (m : Mem) (B : BitVec 32) (o : Nat) {q : Nat} (hq : q < 16) :
    byte (pw m B o) q = m (B.setWidth 64 + BitVec.ofNat 64 (o + q)) := by
  show (m.readW _ 128).extractLsb' (8 * q) 8 = _
  rw [byte_readW _ _ (by omega_arith), Offset.add_ofNat_add_ofNat]

theorem pw_write_self (m : Mem) (B : BitVec 32) (o : Nat) (v : BitVec 128) :
    pw (m.writeW (B.setWidth 64 + BitVec.ofNat 64 o) v) B o = v := Mem.readW_writeW_self _ _ 16 _ (by decide)

/-- The 16 bytes at `o` after a change in the `n` bytes at `a`. -/
theorem pw_frame {m m' : Mem} {B : BitVec 32} {a n o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (ho : o + 16 ≤ a ∨ a + n ≤ o)
    (ha : a + n ≤ 2 ^ 32) (hb : o + 16 ≤ 2 ^ 32) : pw m' B o = pw m B o :=
  hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 o, 16⟩) (Region.contains_self _ 16) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ ho (by omega_arith) (by omega_arith)) (by decide)

theorem byte_frame {m m' : Mem} {B : BitVec 32} {a n o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (ho : o < a ∨ a + n ≤ o)
    (ha : a + n ≤ 2 ^ 32) (hb : o < 2 ^ 32) :
    m' (B.setWidth 64 + BitVec.ofNat 64 o) = m (B.setWidth 64 + BitVec.ofNat 64 o) :=
  hf _ fun r hr hc => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (B.setWidth 64) (d := o) (n := 1) (e := a) (k := n) (by omega_using [ho])
      (by omega_using [hb]) (by omega_using [ha]) _ (Region.contains_self _ 1) hc

/-- A write of 16 bytes at `p` of the scratch buffer. -/
theorem frame_write (m : Mem) (B : BitVec 32) (p : Nat) (v : BitVec 128) :
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 p, 16⟩] m (m.writeW (B.setWidth 64 + BitVec.ofNat 64 p) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)

section
variable {s : State}

/-- Two stores of 16 bytes, at `p₁` and `p₂` of the scratch buffer. -/
def st2 (m : Mem) (B : BitVec 32) (p₁ p₂ : Nat) (v₁ v₂ : BitVec 128) : Mem :=
  (m.writeW (B.setWidth 64 + BitVec.ofNat 64 p₁) v₁).writeW (B.setWidth 64 + BitVec.ofNat 64 p₂) v₂

/-- A step on two registers: the 16 bytes at `o₁` and `o₂` of the scratch
buffer loaded, the step `X` (which only changes XMM registers), and two
registers stored at `p₁` and `p₂`. -/
theorem ld2_st2 {B : BitVec 32} {X : List Instr} {o₁ o₂ p₁ p₂ : Nat} {r₁ r₂ : XReg} (hB : s.gpr sb = B)
    (hs : (⟨B.setWidth 64, 856⟩ : Region) ∈ s.wr) (hf : B.toNat + 856 ≤ 2 ^ 32)
    (ho₁ : o₁ + 16 ≤ 856) (ho₂ : o₂ + 16 ≤ 856) (hp₁ : p₁ + 16 ≤ 856) (hp₂ : p₂ + 16 ≤ 856)
    {P : (XReg → BitVec 128) → Prop}
    (hX : WP isa (.block X) ((s.setXmm .xmm0 (pw s.mem B o₁)).setXmm .xmm1 (pw s.mem B o₂)) fun s' =>
      ∃ f, s' = { s with xmm := f } ∧ P f) :
    WP isa (.block ([ld .xmm0 sb o₁, ld .xmm1 sb o₂] ++ X ++ [stx sb p₁ r₁, stx sb p₂ r₂])) s fun s' =>
      ∃ f, P f ∧ s' = { s with xmm := f, mem := st2 s.mem B p₁ p₂ (f r₁) (f r₂) } := by
  have ad : ∀ o, o + 16 ≤ 856 → addr B o = B.setWidth 64 + BitVec.ofNat 64 o := fun o ho =>
    addr_eq (by omega_using [hf, ho])
  have inw : ∀ o, o + 16 ≤ 856 → ∀ w : List Region, (⟨B.setWidth 64, 856⟩ : Region) ∈ w →
      InRegions w (B.setWidth 64 + BitVec.ofNat 64 o) 16 := fun o ho w hw =>
    ⟨_, hw, Offset.contains_base _ ho (by omega_using [ho])⟩
  show WP isa (.block (ld .xmm0 sb o₁ :: ld .xmm1 sb o₂ :: (X ++ [stx sb p₁ r₁, stx sb p₂ r₂]))) s _
  refine Wp.cons (s' := s.setXmm .xmm0 (pw s.mem B o₁)) ?_
    (Wp.cons (s' := (s.setXmm .xmm0 (pw s.mem B o₁)).setXmm .xmm1 (pw s.mem B o₂)) ?_ ?_)
  · show (State.load128 _ (addr (s.gpr sb) o₁)).map _ = _
    rw [hB, ad o₁ ho₁]
    exact congrArg (Option.map _) (ite_eq_left (inw o₁ ho₁ _ (List.mem_append_right _ hs)))
  · show (State.load128 _ (addr (s.gpr sb) o₂)).map _ = _
    rw [hB, ad o₂ ho₂]
    exact congrArg (Option.map _) (ite_eq_left (inw o₂ ho₂ _ (List.mem_append_right _ hs)))
  refine WP.block_append_iff.mpr (WP.mono hX fun s' ⟨f, e, hP⟩ => ?_)
  subst e
  refine Wp.cons (s' := { s with xmm := f, mem := s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 p₁) (f r₁) }) ?_
    (Wp.cons (s' := { s with xmm := f, mem := st2 s.mem B p₁ p₂ (f r₁) (f r₂) }) ?_ (WP.block_nil ⟨f, hP, rfl⟩))
  · show State.store128 _ (addr (s.gpr sb) p₁) _ = _
    rw [hB, ad p₁ hp₁]
    exact ite_eq_left (inw p₁ hp₁ _ hs)
  · show State.store128 _ (addr (s.gpr sb) p₂) _ = _
    rw [hB, ad p₂ hp₂]
    exact ite_eq_left (inw p₂ hp₂ _ hs)

/-- The bytes at `p₁` and `p₂` after `ld2_st2`'s stores, and what they
leave. -/
theorem st2_mem (m : Mem) (B : BitVec 32) {p₁ p₂ : Nat} (v₁ v₂ : BitVec 128) (hp : p₁ + 16 = p₂)
    (h₂ : p₂ + 16 ≤ 2 ^ 32) :
    pw (st2 m B p₁ p₂ v₁ v₂) B p₁ = v₁ ∧ pw (st2 m B p₁ p₂ v₁ v₂) B p₂ = v₂ ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 p₁, 32⟩] m (st2 m B p₁ p₂ v₁ v₂) := by
  unfold st2
  refine ⟨?_, pw_write_self _ _ _ _, ?_⟩
  · rw [pw_frame (frame_write _ B p₂ v₂) (.inl (by omega_using [hp])) (by omega_using [h₂])
      (by omega_using [hp, h₂]), pw_write_self]
  · exact ((frame_write m B p₁ v₁).sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (Nat.le_refl _) (by omega_arith)⟩).trans
      ((frame_write _ B p₂ v₂).sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_using [hp]) (by omega_using [hp])⟩)

/-- A step on one register: the 16 bytes at `o` of the scratch buffer
loaded, the step `X`, and a register stored there. -/
theorem ld1_st1 {B : BitVec 32} {X : List Instr} {o : Nat} {r : XReg} (hB : s.gpr sb = B)
    (hs : (⟨B.setWidth 64, 856⟩ : Region) ∈ s.wr) (hf : B.toNat + 856 ≤ 2 ^ 32) (ho : o + 16 ≤ 856)
    {P : (XReg → BitVec 128) → Prop}
    (hX : WP isa (.block X) (s.setXmm .xmm0 (pw s.mem B o)) fun s' => ∃ f, s' = { s with xmm := f } ∧ P f) :
    WP isa (.block ([ld .xmm0 sb o] ++ X ++ [stx sb o r])) s fun s' =>
      ∃ f, P f ∧ s' = { s with xmm := f, mem := s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 o) (f r) } := by
  have ad : addr B o = B.setWidth 64 + BitVec.ofNat 64 o := addr_eq (by omega_using [hf, ho])
  have inw : ∀ w : List Region, (⟨B.setWidth 64, 856⟩ : Region) ∈ w →
      InRegions w (B.setWidth 64 + BitVec.ofNat 64 o) 16 := fun w hw =>
    ⟨_, hw, Offset.contains_base _ ho (by omega_using [ho])⟩
  show WP isa (.block (ld .xmm0 sb o :: (X ++ [stx sb o r]))) s _
  refine Wp.cons (s' := s.setXmm .xmm0 (pw s.mem B o)) ?_ ?_
  · show (State.load128 _ (addr (s.gpr sb) o)).map _ = _
    rw [hB, ad]
    exact congrArg (Option.map _) (ite_eq_left (inw _ (List.mem_append_right _ hs)))
  refine WP.block_append_iff.mpr (WP.mono hX fun s' ⟨f, e, hP⟩ => ?_)
  subst e
  refine Wp.cons (s' := { s with xmm := f, mem := s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 o) (f r) }) ?_
    (WP.block_nil ⟨f, hP, rfl⟩)
  show State.store128 _ (addr (s.gpr sb) o) _ = _
  rw [hB, ad]
  exact ite_eq_left (inw _ hs)

/-- What a part leaves of the state it starts in: the general registers,
the flags and the regions as they were, the mask, and `MP` of memory. -/
def Part (s : State) (MP : Mem → Prop) (s' : State) : Prop :=
  (∃ f m, s' = { s with xmm := f, mem := m }) ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ MP s'.mem

theorem xm_trans {s₁ s₂ : State} (e₁ : ∃ f m, s₁ = { s with xmm := f, mem := m })
    (e₂ : ∃ f m, s₂ = { s₁ with xmm := f, mem := m }) : ∃ f m, s₂ = { s with xmm := f, mem := m } := by
  obtain ⟨f, m, rfl⟩ := e₁
  obtain ⟨f', m', rfl⟩ := e₂
  exact ⟨f', m', rfl⟩

/-- A part as it runs computes what it does a pair at a time. -/
theorem transfer {P Q : List Instr} (he : SseEquiv.equiv eparams P Q [(m0, m0)] = true)
    (hp : SseEquiv.Pre eparams s) {MP : Mem → Prop} (hP : WP isa (.block P) s (Part s MP)) :
    WP isa (.block Q) s (Part s MP) :=
  SseEquiv.equiv_wp he hp (WP.mono hP fun sP ⟨_, hm, hM⟩ sQ em ex hs =>
    ⟨hs, fun q hq => by
      rw [show sQ.xmm m0 = sP.xmm m0 from ex (m0, m0) (List.mem_singleton_self _)]; exact hm q hq,
      by rw [em]; exact hM⟩)

end

/-- A state of `crypt` at group `i`, from the state `s₀` it starts in: the
keys' pointer at the group's keys, the table's address, and memory as it
was but in the places and the blocks. -/
structure WAt (s₀ : State) (B : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  frame : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (24 + 112 * i)

section
variable {s₀ s : State} {B : BitVec 32} {i : Nat}

theorem WAt.kr64 (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i) := by
  rw [h.kp]
  exact addr_eq (by omega_arith)

theorem WAt.krNat (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) :
    (s.gpr kr).toNat = B.toNat + (24 + 112 * i) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 24 + 112 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem WAt.adr (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) {o : Nat} (ho : o ≤ 136) :
    addr (s.gpr kr) o = B.setWidth 64 + BitVec.ofNat 64 (24 + (112 * i + o)) := by
  have := h.krNat hf hi
  rw [addr_eq (by omega_arith), h.kr64 hf hi, Offset.add_ofNat_add_ofNat, Nat.add_assoc]

theorem WAt.env (h : WAt s₀ B i s) (hs : ScrIn s₀ B 214) (hi : i < 4) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
    Env s := by
  have hf := hs.fit
  have hn := h.krNat hf hi
  refine ⟨by rw [h.tb, h.syms], by omega_arith, fun o ho =>
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.adr hf hi (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem WAt.key (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) {o : Nat} (ho : o < 136) :
    kb s o = kAt s₀.mem B (112 * i + o) := by
  rw [kb, h.kr64 hf hi, Offset.add_ofNat_add_ofNat, Nat.add_assoc,
    byte_frame h.frame (.inl (by omega_arith)) (by decide) (by omega_arith)]
  rfl

theorem WAt.word (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) {o : Nat} (ho : o + 16 ≤ 136) :
    s.mem.readW (addr (s.gpr kr) o) 128 = wAt s₀.mem B (112 * i + o) := by
  rw [h.adr hf hi (by omega_arith)]
  exact pw_frame h.frame (.inl (by omega_arith)) (by decide) (by omega_arith)

/-- The doublewords of a quadword of the keys, in both quadwords. -/
theorem WAt.kq (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) {o k : Nat} (ho : o + 16 ≤ 136)
    (hk : k < 2) {a c : Nat} (ha : a < 2) (hc : c < 2) :
    dword (kq s (o + 8 * k)) (2 * a + c) = dword (wAt s₀.mem B (112 * i + o)) (2 * k + c) := by
  rw [← h.word hf hi ho, kq, h.adr hf hi (by omega_arith), h.adr hf hi (by omega_arith),
    show 24 + (112 * i + (o + 8 * k)) = 24 + (112 * i + o) + 8 * k by omega_arith, ← Offset.add_ofNat_add_ofNat,
    dword_dupq_readW _ _ hk ha hc]

theorem WAt.part {s' : State} (h : WAt s₀ B i s) (e : ∃ f m, s' = { s with xmm := f, mem := m })
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem s'.mem) : WAt s₀ B i s' := by
  obtain ⟨f, m, rfl⟩ := e
  exact ⟨h.base, h.esp, h.frame.trans hf, h.rd, h.wr, h.syms, h.tb, h.kp⟩

/-- A general register written by an instruction that leaves the others,
memory and the XMM registers. -/
theorem WAt.upd {s' : State} {d : Reg} {v : BitVec 32} (h : WAt s₀ B i s) (u : Wp.Upd s s' d v)
    (hd : d ≠ sb ∧ d ≠ .esp ∧ d ≠ tbr ∧ d ≠ kr) : WAt s₀ B i s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1)]; exact h.base, by rw [u.other _ (Ne.symm hd.2.1)]; exact h.esp,
    by rw [u.mem]; exact h.frame, u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms,
    by rw [u.other _ (Ne.symm hd.2.2.1)]; exact h.tb, by rw [u.other _ (Ne.symm hd.2.2.2)]; exact h.kp⟩

theorem WAt.gk {g : Nat} {E : Nat → BitVec 64} (h : WAt s₀ B i s) (hs : ScrIn s₀ B 214)
    (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4) : AesNi.GroupKeys s (fun r => E (2 + 8 * i + r)) :=
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  ⟨fun r hr j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk i hi r hr j hj,
    fun j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk4 i hi j hj,
    fun j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk5 i hi j hj⟩

/-- What the parts as they run need of the state. -/
theorem WAt.pre (h : WAt s₀ B i s) (hs : ScrIn s₀ B 214) (hi : i < 4) : SseEquiv.Pre eparams s := by
  have hf := hs.fit
  have hn := h.krNat hf hi
  have hb : (s.gpr sb).toNat = B.toNat := by rw [h.base]
  have ad : ∀ o, o ≤ 640 → addr (s.gpr sb) o = B.setWidth 64 + BitVec.ofNat 64 o := fun o ho => by
    rw [h.base]; exact addr_eq (by omega_arith)
  refine ⟨by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms], by show (s.gpr sb).toNat + 640 ≤ _; omega_arith,
    by show (s.gpr kr).toNat + 128 ≤ _; omega_arith, Nat.le_refl _, fun o n ho => ?_, fun o _ ho => ?_,
    fun o n ho => ?_, ?_⟩
  · have ho : o + n ≤ 640 := ho
    refine ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩
    show Region.Contains _ (addr (s.gpr sb) o) n
    rw [ad o (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · have ho : o + 16 ≤ 640 := ho
    refine ⟨_, by rw [h.wr]; exact hs.wr, ?_⟩
    show Region.Contains _ (addr (s.gpr sb) o) 16
    rw [ad o (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · have ho : o + n ≤ 128 := ho
    refine ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩
    show Region.Contains _ (addr (s.gpr kr) o) n
    rw [h.adr hf hi (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨(s.gpr kr).setWidth 64, 128⟩ ⟨(s.gpr sb).setWidth 64 + BitVec.ofNat 64 512, 640 - 512⟩
    rw [h.kr64 hf hi, h.base]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by decide)

end

end

end VG.Proof.Camellia.X86.AesNiWide
