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
      (∀ L < 2, ∀ q < 16, byte (s'.xmm (if L = 0 then .xmm0 else .xmm2)) q =
        qI (isA (slot (bswq q % 8)))
          (if bswq q < 8 then byte (s.xmm .xmm1) (8 * L + bswq q) ^^^ kb s (56 + bswq q)
            else byte (s.xmm .xmm0) (8 * L + (bswq q - 8))) ^^^ kb s (64 + q)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := conv_all.2.2.2.2.2
  unfold joinOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨h0, h2⟩, c0⟩, c2⟩, hm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun L hL q hq => ?_, AesNi.rel_mask hr hm⟩
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

/-- The scratch buffer of the core's 214 slots. -/
abbrev Scr (s : State) (B : BitVec 32) : Prop := VG.Proof.Modes.X86.ScrIn s B 214

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

theorem WAt.env (h : WAt s₀ B i s) (hs : Scr s₀ B) (hi : i < 4) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
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
theorem WAt.dword_kq (h : WAt s₀ B i s) (hf : B.toNat + 856 ≤ 2 ^ 32) (hi : i < 4) {o k : Nat} (ho : o + 16 ≤ 136)
    (hk : k < 2) {a c : Nat} (ha : a < 2) (hc : c < 2) :
    dword (kq s (o + 8 * k)) (2 * a + c) = dword (wAt s₀.mem B (112 * i + o)) (2 * k + c) := by
  rw [← h.word hf hi ho, AesNiWide.kq, h.adr hf hi (by omega_arith), h.adr hf hi (by omega_arith),
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

theorem WAt.gk {g : Nat} {E : Nat → BitVec 64} (h : WAt s₀ B i s) (hs : Scr s₀ B)
    (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4) : AesNi.GroupKeys s (fun r => E (2 + 8 * i + r)) :=
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  ⟨fun r hr j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk i hi r hr j hj,
    fun j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk4 i hi j hj,
    fun j hj => by have := slot_lt j; rw [h.key hf hi4 (by omega_arith)]; exact hk.rk5 i hi j hj⟩

/-- What the parts as they run need of the state. -/
theorem WAt.pre (h : WAt s₀ B i s) (hs : Scr s₀ B) (hi : i < 4) : SseEquiv.Pre eparams s := by
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

/-! ### The rounds of a group -/

section
variable {s₀ s : State} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64}

/-- The halves `d b` of the four blocks, in the rounds' form with the first
two subkeys of group `i`, in the places: block `2 p + L` in quadword `L` of
pair `p`'s. -/
def HalvesAt (m : Mem) (B : BitVec 32) (E : Nat → BitVec 64) (i : Nat) (d : Nat → BitVec 64 × BitVec 64) : Prop :=
  ∀ p < 2, Lanes (pw m B (plc p 0)) (fun L j => dq (d (2 * p + L)).1 j ^^^ dq (E (2 + 8 * i)) j ^^^ c5) ∧
    Lanes (pw m B (plc p 1)) (fun L j => dq (d (2 * p + L)).2 j ^^^ dq (E (2 + 8 * i + 1)) j ^^^ c5 ^^^ gc j)

/-- The halves `P b` in the rounds' form, in the places, the second with
the key `K` of the group's last round. -/
def TriAt (m : Mem) (B : BitVec 32) (K : BitVec 64) (P : Nat → BitVec 64 × BitVec 64) : Prop :=
  ∀ p < 2, Lanes (pw m B (plc p 0)) (fun L => dq (P (2 * p + L)).1) ∧
    Lanes (pw m B (plc p 1)) (fun L j => dq (P (2 * p + L)).2 j ^^^ dq K j ^^^ c5)

theorem plc_le {p h : Nat} (hp : p < 2) (hh : h < 2) : plc p h + 16 ≤ 576 ∧ 512 ≤ plc p h := by
  unfold plc; omega_arith

/-- The six rounds of group `i` on pair `p`. -/
theorem pairGroup_wp {p : Nat} (hp : p < 2) (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4)
    (h : WAt s₀ B i s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {a b : Nat → BitVec 64}
    (h0 : Lanes (pw s.mem B (plc p 0)) fun L j => dq (a L) j ^^^ dq (E (2 + 8 * i)) j ^^^ c5)
    (h1 : Lanes (pw s.mem B (plc p 1)) fun L j => dq (b L) j ^^^ dq (E (2 + 8 * i + 1)) j ^^^ c5 ^^^ gc j) :
    WP isa (.block (pairGroup p)) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p 0), 32⟩] s.mem m ∧
      Lanes (pw m B (plc p 0)) (fun L => dq (AesNi.tri E i (a L, b L)).1) ∧
      Lanes (pw m B (plc p 1)) (fun L j => dq (AesNi.tri E i (a L, b L)).2 j ^^^ dq (E (2 + 8 * i + 5)) j ^^^ c5)) := by
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  have he := h.env hs hi4 hm
  have hK := h.gk hs hk hi hg
  have l0 := plc_le hp (show 0 < 2 by decide)
  have l1 := plc_le hp (show 1 < 2 by decide)
  refine WP.mono (ld2_st2 (r₁ := .xmm0) (r₂ := .xmm1) (X := rounds6) (P := fun f =>
      (∀ q < 16, byte (f m0) q = 0x0f#8) ∧ Lanes (f .xmm0) (fun L => dq (AesNi.tri E i (a L, b L)).1) ∧
      Lanes (f .xmm1) (fun L j => dq (AesNi.tri E i (a L, b L)).2 j ^^^ dq (E (2 + 8 * i + 5)) j ^^^ c5))
    h.base (by rw [h.wr]; exact hs.wr) hf (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) ?_) ?_
  · refine WP.mono (rounds6_wp (s := (s.setXmm .xmm0 (pw s.mem B (plc p 0))).setXmm .xmm1 (pw s.mem B (plc p 1)))
      (k := fun r => E (2 + 8 * i + r)) (a := a) (b := b)
      ⟨he.tb, he.fit, he.acc, hm⟩ ⟨hK.d, hK.d4, hK.d5⟩ h0 h1) fun s' ⟨⟨f, e⟩, he', x, y⟩ => ⟨f, e, ?_⟩
    subst e
    exact ⟨he'.msk, x, y⟩
  · rintro s' ⟨f, ⟨hm', x, y⟩, rfl⟩
    obtain ⟨r1, r2, fr⟩ := st2_mem s.mem B (f .xmm0) (f .xmm1) (show plc p 0 + 16 = plc p 1 from rfl)
      (by omega_arith)
    exact ⟨⟨f, _, rfl⟩, hm', fr, by rw [r1]; exact x, by rw [r2]; exact y⟩

theorem two {p : Nat} (hp : p < 2) : p = 0 ∨ p = 1 := by omega_arith

/-- The 32 bytes of a pair's places are among the places and the blocks. -/
theorem sub_places {p : Nat} (hp : p < 2) {m m' : Mem}
    (h : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p 0), 32⟩] m m') :
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    have := plc_le hp (show 0 < 2 by decide)
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ this.2 (by unfold plc at this ⊢; omega_arith)⟩

/-- The six rounds of group `i`, a pair at a time. -/
theorem refGroup_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4) (h : WAt s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {d : Nat → BitVec 64 × BitVec 64}
    (hh : HalvesAt s.mem B E i d) :
    WP isa (.block refGroup) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem m ∧
      TriAt m B (E (2 + 8 * i + 5)) (fun b => AesNi.tri E i (d b))) := by
  refine WP.block_append_iff.mpr (WP.mono (pairGroup_wp (p := 0) (by decide) hs hk hi hg h hm
    (a := fun L => (d (2 * 0 + L)).1) (b := fun L => (d (2 * 0 + L)).2) (hh 0 (by decide)).1 (hh 0 (by decide)).2)
    fun s₁ ⟨e₁, m₁, F₁, x₁, y₁⟩ => ?_)
  have a₁ := h.part e₁ (sub_places (by decide) F₁)
  have q0 : pw s₁.mem B (plc 1 0) = pw s.mem B (plc 1 0) := pw_frame F₁ (.inr (by decide)) (by decide) (by decide)
  have q1 : pw s₁.mem B (plc 1 1) = pw s.mem B (plc 1 1) := pw_frame F₁ (.inr (by decide)) (by decide) (by decide)
  refine WP.mono (pairGroup_wp (p := 1) (by decide) hs hk hi hg a₁ m₁
    (a := fun L => (d (2 * 1 + L)).1) (b := fun L => (d (2 * 1 + L)).2) (by rw [q0]; exact (hh 1 (by decide)).1)
    (by rw [q1]; exact (hh 1 (by decide)).2)) fun s₂ ⟨e₂, m₂, F₂, x₂, y₂⟩ => ?_
  refine ⟨xm_trans e₁ e₂, m₂, (sub_places (by decide) F₁).trans (sub_places (by decide) F₂), fun p hp => ?_⟩
  rcases two hp with rfl | rfl
  · rw [pw_frame F₂ (.inl (by decide)) (by decide) (by decide),
      pw_frame F₂ (.inl (by decide)) (by decide) (by decide)]
    exact ⟨x₁, y₁⟩
  · exact ⟨x₂, y₂⟩

/-- The six rounds of group `i` and the count of the groups left. -/
theorem rounds_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4) (h : WAt s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {d : Nat → BitVec 64 × BitVec 64}
    (hh : HalvesAt s.mem B E i d) {n : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    WP isa (.block rounds) s fun s' => WAt s₀ B i s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - 1) ∧ s'.zf = some (decide (n = 1)) ∧
      TriAt s'.mem B (E (2 + 8 * i + 5)) (fun b => AesNi.tri E i (d b)) := by
  refine WP.block_append_iff.mpr (WP.mono (transfer group_equiv (h.pre hs (by omega_arith))
    (refGroup_wp hs hk hi hg h hm hh)) fun s₁ ⟨e₁, m₁, F₁, t₁⟩ => ?_)
  have a₁ := h.part e₁ F₁
  have c₁ : s₁.gpr .ecx = BitVec.ofNat 32 n := by obtain ⟨f, m, rfl⟩ := e₁; exact hc
  refine AesNi.wp_subi_x fun s₂ u₂ xe z₂ => WP.block_nil ?_
  refine ⟨a₁.upd u₂ (by decide), by rw [xe]; exact m₁, ?_, ?_, by rw [u₂.mem]; exact t₁⟩
  · rw [u₂.gpr, c₁]; exact Wp.ofNat_pred hn
  · rw [z₂, c₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]

end

/-! ### The FL layer -/

section
variable {s₀ s : State} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64}

/-- FL (`h = 0`) or FL⁻¹ (`h = 1`) of the half `A L` in each quadword of
pair `p`'s place `h`, into the next group's form. -/
theorem halfLayer_wp {p h : Nat} (hp : p < 2) (hh : h = 0 ∨ h = 1) (hs : Scr s₀ B) (hk : Keys s₀.mem B g E)
    (hi : i + 1 < g) (hg : g ≤ 4) (hw : WAt s₀ B i s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {A : Nat → BitVec 64}
    (hv : Lanes (pw s.mem B (plc p h)) fun L j => dq (A L) j ^^^ (if h = 1 then kb s (56 + slot j) else 0#8)) :
    WP isa (.block (halfLayer (plc p h) h)) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p h), 16⟩] s.mem m ∧
      Lanes (pw m B (plc p h)) (fun L j =>
        dq (if h = 0 then Spec.Camellia.fl (A L) (E (8 + 8 * i)) else Spec.Camellia.flinv (A L) (E (9 + 8 * i))) j ^^^
          kb s (112 + 8 * h + slot j))) := by
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  have he := hw.env hs hi4 hm
  have hh2 : h < 2 := by rcases hh with rfl | rfl <;> decide
  have l := plc_le hp hh2
  refine WP.mono (ld1_st1 (r := .xmm1) (X := halfIn h ++ halfMid h ++ halfOut h) (P := fun f =>
      (∀ q < 16, byte (f m0) q = 0x0f#8) ∧ Lanes (f .xmm1) (fun L j =>
        dq (if h = 0 then Spec.Camellia.fl (A L) (E (8 + 8 * i)) else Spec.Camellia.flinv (A L) (E (9 + 8 * i))) j ^^^
          kb s (112 + 8 * h + slot j)))
    hw.base (by rw [hw.wr]; exact hs.wr) hf (by omega_arith) ?_) ?_
  · have he₁ : Env (s.setXmm .xmm0 (pw s.mem B (plc p h))) := ⟨he.tb, he.fit, he.acc, hm⟩
    refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (halfIn_wp hh he₁) fun s₂ ⟨e₂, v₂, m₂⟩ => ?_))
    have he₂ := he₁.same e₂ m₂
    obtain ⟨f₂, rfl⟩ := e₂
    have hv₂ : f₂ .xmm3 = AesNi.hl (A 0) (A 1) := AesNi.eq_hl fun j hj => by
      have sj := slot_lt j
      have a0 := hv 0 (by decide) j hj
      have a1 := hv 1 (by decide) j hj
      rw [Nat.mul_zero, Nat.zero_add] at a0
      rw [show 8 * 1 + slot j = slot j + 8 by omega_arith] at a1
      refine ⟨?_, ?_⟩
      · refine (v₂ _ (by omega_arith)).trans ?_
        rw [show slot j % 8 = slot j by omega_arith, slot_slot hj]
        show qI (isA j) (byte (pw s.mem B (plc p h)) (slot j) ^^^ (if h = 1 then kb s (56 + slot j) else 0#8)) = _
        rw [a0, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        exact AesNi.qI_qT _ _
      · refine (v₂ _ (by omega_arith)).trans ?_
        rw [show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj]
        show qI (isA j) (byte (pw s.mem B (plc p h)) (slot j + 8) ^^^ (if h = 1 then kb s (56 + slot j) else 0#8)) = _
        rw [a1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        exact AesNi.qI_qT _ _
    refine WP.mono (halfMid_wp hh he₂) fun s₃ ⟨e₃, he₃, v₃⟩ => ?_
    obtain ⟨f₃, rfl⟩ := e₃
    have hv₃ : f₃ .xmm3 = if h = 0 then AesNi.hl (Spec.Camellia.fl (A 0) (E (8 + 8 * i))) (Spec.Camellia.fl (A 1) (E (8 + 8 * i)))
        else AesNi.hl (Spec.Camellia.flinv (A 0) (E (9 + 8 * i))) (Spec.Camellia.flinv (A 1) (E (9 + 8 * i))) := by
      refine v₃.trans ?_
      show fl3 (f₂ .xmm3) _ _ _ = _
      rw [hv₂]
      exact fl3_half hh (hk.fl i hi) (A 0) (A 1)
        (fun a ha c hc => hw.dword_kq hf hi4 (o := 64) (by decide) hh2 ha hc)
        (fun a ha c hc => hw.dword_kq hf hi4 (o := 96) (by decide) hh2 ha hc)
        (fun a ha c hc => hw.dword_kq hf hi4 (o := 80) (by decide) hh2 ha hc)
    refine WP.mono (halfOut_wp hh he₃) fun s₄ ⟨e₄, v₄, m₄⟩ => ?_
    obtain ⟨f₄, rfl⟩ := e₄
    refine ⟨f₄, rfl, m₄, fun L hL j hj => ?_⟩
    obtain ⟨h16, h8, _⟩ := lane_idx (j := j) hL
    refine (v₄ _ h16).trans ?_
    rw [h8, slot_slot hj]
    show qT (isA j) (byte (f₃ .xmm3) (8 * L + slot j)) ^^^ kb s (112 + 8 * h + slot j) =
      dq (if h = 0 then Spec.Camellia.fl (A L) (E (8 + 8 * i)) else Spec.Camellia.flinv (A L) (E (9 + 8 * i))) j ^^^
        kb s (112 + 8 * h + slot j)
    rw [hv₃]
    rcases hh with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      rcases two hL with rfl | rfl
      · rw [Nat.mul_zero, Nat.zero_add, (AesNi.byte_hl _ _ hj).1]; rfl
      · rw [show 8 * 1 + slot j = slot j + 8 by omega_arith, (AesNi.byte_hl _ _ hj).2]; rfl
    · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
      rcases two hL with rfl | rfl
      · rw [Nat.mul_zero, Nat.zero_add, (AesNi.byte_hl _ _ hj).1]; rfl
      · rw [show 8 * 1 + slot j = slot j + 8 by omega_arith, (AesNi.byte_hl _ _ hj).2]; rfl
  · rintro s' ⟨f, ⟨hm', y⟩, rfl⟩
    exact ⟨⟨f, _, rfl⟩, hm', frame_write _ _ _ _, by rw [pw_write_self]; exact y⟩

/-- The 16 bytes of a place are among the places and the blocks. -/
theorem sub_place {p h : Nat} (hp : p < 2) (hh : h < 2) {m m' : Mem}
    (hF : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p h), 16⟩] m m') :
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p 0), 32⟩] m m' :=
  hF.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by unfold plc; omega_arith) (by unfold plc; omega_arith)⟩

/-- The FL layer after group `i` on pair `p`: FL of its first halves, and
FL⁻¹ of its second, which first take the last round's key. -/
theorem pairLayer_wp {p : Nat} (hp : p < 2) (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i + 1 < g) (hg : g ≤ 4)
    (h : WAt s₀ B i s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {a b : Nat → BitVec 64}
    (h0 : Lanes (pw s.mem B (plc p 0)) fun L => dq (a L))
    (h1 : Lanes (pw s.mem B (plc p 1)) fun L j => dq (b L) j ^^^ dq (E (2 + 8 * i + 5)) j ^^^ c5) :
    WP isa (.block (pairLayer p)) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p 0), 32⟩] s.mem m ∧
      Lanes (pw m B (plc p 0)) (fun L j =>
        dq (Spec.Camellia.fl (a L) (E (8 + 8 * i))) j ^^^ dq (E (2 + 8 * (i + 1))) j ^^^ c5) ∧
      Lanes (pw m B (plc p 1)) (fun L j =>
        dq (Spec.Camellia.flinv (b L) (E (9 + 8 * i))) j ^^^ dq (E (2 + 8 * (i + 1) + 1)) j ^^^ c5 ^^^ gc j)) := by
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  refine WP.block_append_iff.mpr (WP.mono (halfLayer_wp (h := 0) (A := a) hp (.inl rfl) hs hk hi hg h hm
    (h0.congr fun L _ j _ => by rw [ite_eq_right (by decide), BitVec.xor_zero])) fun s₁ ⟨e₁, m₁, F₁, x₁⟩ => ?_)
  have a₁ := h.part e₁ (sub_places hp (sub_place hp (by decide) F₁))
  have q1 : pw s₁.mem B (plc p 1) = pw s.mem B (plc p 1) :=
    pw_frame F₁ (.inr (by unfold plc; omega_arith)) (by unfold plc; omega_arith) (by unfold plc; omega_arith)
  have k56 : ∀ j < 8, kb s₁ (56 + slot j) = dq (E (2 + 8 * i + 5)) j ^^^ c5 := fun j hj => by
    have := slot_lt j
    rw [a₁.key hf hi4 (by omega_arith)]; exact hk.rk5 i (by omega_arith) j hj
  refine WP.mono (halfLayer_wp (h := 1) (A := b) hp (.inr rfl) hs hk hi hg a₁ m₁ (by
    rw [q1]
    exact h1.congr fun L _ j hj => by rw [ite_eq_left rfl, k56 j hj, BitVec.xor_assoc])) fun s₂ ⟨e₂, m₂, F₂, y₂⟩ => ?_
  refine ⟨xm_trans e₁ e₂, m₂, (sub_place hp (by decide) F₁).trans (sub_place hp (by decide) F₂), ?_, ?_⟩
  · rw [pw_frame F₂ (.inl (by unfold plc; omega_arith)) (by unfold plc; omega_arith) (by unfold plc; omega_arith)]
    refine x₁.congr fun L _ j hj => ?_
    have := slot_lt j
    rw [ite_eq_left rfl, show 112 + 8 * 0 + slot j = 112 + slot j by omega_arith, h.key hf hi4 (by omega_arith),
      (hk.kin i hi j hj).1, BitVec.xor_assoc]
  · refine y₂.congr fun L _ j hj => ?_
    have := slot_lt j
    rw [ite_eq_right (by decide), show 112 + 8 * 1 + slot j = 120 + slot j by omega_arith,
      a₁.key hf hi4 (by omega_arith), (hk.kin i hi j hj).2]
    simp only [BitVec.xor_assoc]

/-- The FL layer after group `i`, a pair at a time. -/
theorem refLayer_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i + 1 < g) (hg : g ≤ 4) (h : WAt s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {P : Nat → BitVec 64 × BitVec 64}
    (ht : TriAt s.mem B (E (2 + 8 * i + 5)) P) :
    WP isa (.block refLayer) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem m ∧
      HalvesAt m B E (i + 1) (fun b => (Spec.Camellia.fl (P b).1 (E (8 + 8 * i)), Spec.Camellia.flinv (P b).2 (E (9 + 8 * i))))) := by
  refine WP.block_append_iff.mpr (WP.mono (pairLayer_wp (p := 0) (by decide) hs hk hi hg h hm
    (a := fun L => (P (2 * 0 + L)).1) (b := fun L => (P (2 * 0 + L)).2) (ht 0 (by decide)).1 (ht 0 (by decide)).2)
    fun s₁ ⟨e₁, m₁, F₁, x₁, y₁⟩ => ?_)
  have a₁ := h.part e₁ (sub_places (by decide) F₁)
  have q0 : pw s₁.mem B (plc 1 0) = pw s.mem B (plc 1 0) := pw_frame F₁ (.inr (by decide)) (by decide) (by decide)
  have q1 : pw s₁.mem B (plc 1 1) = pw s.mem B (plc 1 1) := pw_frame F₁ (.inr (by decide)) (by decide) (by decide)
  refine WP.mono (pairLayer_wp (p := 1) (by decide) hs hk hi hg a₁ m₁
    (a := fun L => (P (2 * 1 + L)).1) (b := fun L => (P (2 * 1 + L)).2) (by rw [q0]; exact (ht 1 (by decide)).1)
    (by rw [q1]; exact (ht 1 (by decide)).2)) fun s₂ ⟨e₂, m₂, F₂, x₂, y₂⟩ => ?_
  refine ⟨xm_trans e₁ e₂, m₂, (sub_places (by decide) F₁).trans (sub_places (by decide) F₂), fun p hp => ?_⟩
  rcases two hp with rfl | rfl
  · rw [pw_frame F₂ (.inl (by decide)) (by decide) (by decide),
      pw_frame F₂ (.inl (by decide)) (by decide) (by decide)]
    exact ⟨x₁, y₁⟩
  · exact ⟨x₂, y₂⟩

/-- FL and FL⁻¹ after group `i`, into the next group's form. -/
theorem layer_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hi : i + 1 < g) (hg : g ≤ 4) (h : WAt s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {P : Nat → BitVec 64 × BitVec 64}
    (ht : TriAt s.mem B (E (2 + 8 * i + 5)) P) {n : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hn : 1 ≤ n)
    (hn4 : n ≤ 4) :
    WP isa (.block layer) s fun s' => WAt s₀ B (i + 1) s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 n ∧ s'.zf = some false ∧
      HalvesAt s'.mem B E (i + 1) (fun b => (Spec.Camellia.fl (P b).1 (E (8 + 8 * i)), Spec.Camellia.flinv (P b).2 (E (9 + 8 * i)))) := by
  refine WP.block_append_iff.mpr (WP.mono (transfer layer_equiv (h.pre hs (by omega_arith))
    (refLayer_wp hs hk hi hg h hm ht)) fun s₃ ⟨e₃, m₃, F₃, h₃⟩ => ?_)
  have a₃ := h.part e₃ F₃
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by obtain ⟨f, m, rfl⟩ := e₃; exact hc
  refine AesNi.wp_addi_x fun s₄ u₄ xe₄ => AesNi.wp_test_x fun s₅ u₅ xe₅ z₅ => WP.block_nil ?_
  have x₅ : s₅.xmm = s₃.xmm := xe₅.trans xe₄
  refine ⟨⟨?_, ?_, by rw [u₅.mem, u₄.mem]; exact a₃.frame, u₅.rd.trans (u₄.rd.trans a₃.rd),
    u₅.wr.trans (u₄.wr.trans a₃.wr), u₅.syms.trans (u₄.syms.trans a₃.syms), ?_, ?_⟩, by rw [x₅]; exact m₃, ?_, ?_,
    by rw [u₅.mem, u₄.mem]; exact h₃⟩
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.base
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.esp
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.tb
  · rw [u₅.gpr, u₄.gpr, a₃.kp, show (112 : BitVec 32) = BitVec.ofNat 32 112 from rfl, Offset.add_ofNat_add_ofNat,
      show 24 + 112 * i + 112 = 24 + 112 * (i + 1) by omega_arith]
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact c₃
  · rw [z₅, u₄.other _ (by decide), c₃, BitVec.and_self, Wp.ofNat_beq_zero (by omega_arith),
      decide_eq_false (by omega_arith)]

end

/-! ### The blocks to the places, and back -/

section
variable {s₀ s : State} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64}

theorem blk_le {b : Nat} (hb : b < 4) : blk b + 16 ≤ 640 ∧ 576 ≤ blk b := by unfold blk; omega_arith

/-- Pair `p`'s two blocks to its places, in the rounds' form with the first
keys. -/
theorem pairIn_wp {p : Nat} (hp : p < 2) (hs : Scr s₀ B) (h : WAt s₀ B 0 s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
    WP isa (.block (pairIn p)) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (plc p 0), 32⟩] s.mem m ∧
      ∀ L < 2, ∀ r < 8,
        byte (pw m B (plc p 0)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq r))) ^^^
            kAt s₀.mem B r ∧
        byte (pw m B (plc p 1)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq (r + 8)))) ^^^
            kAt s₀.mem B (8 + r)) := by
  have hf := hs.fit
  have he := h.env hs (by decide) hm
  have b0 := blk_le (b := 2 * p) (by omega_arith)
  have b1 := blk_le (b := 2 * p + 1) (by omega_arith)
  have l0 := plc_le hp (show 0 < 2 by decide)
  have l1 := plc_le hp (show 1 < 2 by decide)
  refine WP.mono (ld2_st2 (r₁ := .xmm3) (r₂ := .xmm1) (X := inX) (o₁ := blk (2 * p)) (o₂ := blk (2 * p + 1))
    (P := fun f => (∀ q < 16, byte (f m0) q = 0x0f#8) ∧
      (∀ q < 16, byte (f .xmm3) q = qT (isA (slot (q % 8)))
        (byte (pw s.mem B (blk (2 * p + q / 8))) (bswq (q % 8))) ^^^ kb s (q % 8)) ∧
      (∀ q < 16, byte (f .xmm1) q = qT (isA (slot (q % 8)))
        (byte (pw s.mem B (blk (2 * p + q / 8))) (bswq (q % 8 + 8))) ^^^ kb s (8 + q % 8)))
    h.base (by rw [h.wr]; exact hs.wr) hf (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) ?_) ?_
  · refine WP.mono (inX_wp
      (s := (s.setXmm .xmm0 (pw s.mem B (blk (2 * p)))).setXmm .xmm1 (pw s.mem B (blk (2 * p + 1))))
      ⟨he.tb, he.fit, he.acc, hm⟩) fun s' ⟨⟨f, e⟩, v3, v1, m'⟩ => ⟨f, e, ?_⟩
    subst e
    have reg : ∀ q < 16,
        ((s.setXmm .xmm0 (pw s.mem B (blk (2 * p)))).setXmm .xmm1 (pw s.mem B (blk (2 * p + 1)))).xmm (xreg (q / 8)) =
          pw s.mem B (blk (2 * p + q / 8)) := fun q hq => by
      have : q / 8 = 0 ∨ q / 8 = 1 := by omega_arith
      rcases this with e | e <;> rw [e] <;> rfl
    exact ⟨m', fun q hq => by rw [v3 q hq, reg q hq]; rfl, fun q hq => by rw [v1 q hq, reg q hq]; rfl⟩
  · rintro s' ⟨f, ⟨hm', v3, v1⟩, rfl⟩
    obtain ⟨r1, r2, fr⟩ := st2_mem s.mem B (f .xmm3) (f .xmm1) (show plc p 0 + 16 = plc p 1 from rfl)
      (by omega_arith)
    refine ⟨⟨f, _, rfl⟩, hm', fr, fun L hL r hr => ?_⟩
    have h16 : 8 * L + r < 16 := by omega_arith
    rw [r1, r2, v3 _ h16, v1 _ h16, show (8 * L + r) % 8 = r by omega_arith,
      show (8 * L + r) / 8 = L by omega_arith, byte_pw _ _ _ (AesNi.bswq_lt (show r < 16 by omega_arith)),
      byte_pw _ _ _ (AesNi.bswq_lt (show r + 8 < 16 by omega_arith)), h.key hf (by decide) (by omega_arith),
      h.key hf (by decide) (by omega_arith), Nat.mul_zero, Nat.zero_add, Nat.zero_add]
    exact ⟨rfl, rfl⟩

/-- The four blocks to the places, a pair at a time. -/
theorem refIn_wp (hs : Scr s₀ B) (h : WAt s₀ B 0 s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
    WP isa (.block refIn) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem m ∧
      ∀ p < 2, ∀ L < 2, ∀ r < 8,
        byte (pw m B (plc p 0)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq r))) ^^^
            kAt s₀.mem B r ∧
        byte (pw m B (plc p 1)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq (r + 8)))) ^^^
            kAt s₀.mem B (8 + r)) := by
  refine WP.block_append_iff.mpr (WP.mono (pairIn_wp (p := 0) (by decide) hs h hm)
    fun s₁ ⟨e₁, m₁, F₁, x₁⟩ => ?_)
  have a₁ := h.part e₁ (sub_places (by decide) F₁)
  refine WP.mono (pairIn_wp (p := 1) (by decide) hs a₁ m₁) fun s₂ ⟨e₂, m₂, F₂, x₂⟩ => ?_
  refine ⟨xm_trans e₁ e₂, m₂, (sub_places (by decide) F₁).trans (sub_places (by decide) F₂),
    fun p hp L hL r hr => ?_⟩
  rcases two hp with rfl | rfl
  · rw [pw_frame F₂ (.inl (by decide)) (by decide) (by decide),
      pw_frame F₂ (.inl (by decide)) (by decide) (by decide)]
    exact x₁ L hL r hr
  · have b := blk_le (b := 2 * 1 + L) (by omega_arith)
    have q0 := AesNi.bswq_lt (show r < 16 by omega_arith)
    have q1 := AesNi.bswq_lt (show r + 8 < 16 by omega_arith)
    have := x₂ L hL r hr
    rw [byte_frame F₁ (.inr (by unfold plc; omega_arith)) (by decide) (by omega_arith),
      byte_frame F₁ (.inr (by unfold plc; omega_arith)) (by decide) (by omega_arith)] at this
    exact this

/-- The mask, from the table. -/
theorem m0_wp (htb : s.gpr tbr = s.syms tableName) (hfit : (s.gpr kr).toNat + 136 ≤ 2 ^ 32)
    (hacc : ∀ o, o + 16 ≤ 136 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16) :
    WP isa (.block [tb m0 wM0]) s fun s' => Same s s' ∧ ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := by
  have hok := m0_ok
  unfold m0Ok at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  exact run_wp (rel_init (p := wparams) htb hfit hacc) hrun fun s' hr hs => ⟨hs, AesNi.rel_mask hr hok⟩

theorem bswq_rev {j : Nat} (hj : j < 8) : bswq (7 - j) = slot j ∧ bswq (15 - j) = slot j + 8 := by
  unfold bswq slot
  constructor <;> (repeat' split) <;> omega_arith

theorem xor4 (b k c : Byte) : b ^^^ k ^^^ c ^^^ (k ^^^ c) = b := by
  rw [BitVec.xor_assoc b k c, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Pair `p`'s halves after the last round, the second with that round's
key, to its two blocks, with the last two subkeys. -/
theorem pairOut_wp {p : Nat} (hp : p < 2) (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hg1 : 1 ≤ g) (hg : g ≤ 4)
    (h : WAt s₀ B (g - 1) s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {a b : Nat → BitVec 64}
    (h0 : Lanes (pw s.mem B (plc p 0)) fun L => dq (a L))
    (h1 : Lanes (pw s.mem B (plc p 1)) fun L j => dq (b L) j ^^^ dq (E (2 + 8 * (g - 1) + 5)) j ^^^ c5) :
    WP isa (.block (pairOut p)) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p)), 32⟩] s.mem m ∧
      ∀ L < 2, ∀ j < 8, byte (pw m B (blk (2 * p + L))) (7 - j) = bz (b L ^^^ E (8 * g)) j ∧
        byte (pw m B (blk (2 * p + L))) (15 - j) = bz (a L ^^^ E (8 * g + 1)) j) := by
  have hf := hs.fit
  have hi4 : g - 1 < 4 := by omega_arith
  have he := h.env hs hi4 hm
  have b0 := blk_le (b := 2 * p) (by omega_arith)
  have b1 := blk_le (b := 2 * p + 1) (by omega_arith)
  have l0 := plc_le hp (show 0 < 2 by decide)
  have l1 := plc_le hp (show 1 < 2 by decide)
  have k56 : ∀ j < 8, kb s (56 + slot j) = dq (E (2 + 8 * (g - 1) + 5)) j ^^^ c5 := fun j hj => by
    have := slot_lt j
    rw [h.key hf hi4 (by omega_arith)]; exact hk.rk5 (g - 1) (by omega_arith) j hj
  refine WP.mono (ld2_st2 (r₁ := .xmm0) (r₂ := .xmm2) (X := joinX) (o₁ := plc p 0) (o₂ := plc p 1)
    (p₁ := blk (2 * p)) (p₂ := blk (2 * p + 1))
    (P := fun f => (∀ q < 16, byte (f m0) q = 0x0f#8) ∧ ∀ L < 2, ∀ j < 8,
      byte (f (if L = 0 then .xmm0 else .xmm2)) (7 - j) = bz (b L ^^^ E (8 * g)) j ∧
      byte (f (if L = 0 then .xmm0 else .xmm2)) (15 - j) = bz (a L ^^^ E (8 * g + 1)) j)
    h.base (by rw [h.wr]; exact hs.wr) hf (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) ?_) ?_
  · refine WP.mono (join_wp
      (s := (s.setXmm .xmm0 (pw s.mem B (plc p 0))).setXmm .xmm1 (pw s.mem B (plc p 1)))
      ⟨he.tb, he.fit, he.acc, hm⟩) fun s' ⟨⟨f, e⟩, v, m'⟩ => ⟨f, e, ?_⟩
    subst e
    refine ⟨m', fun L hL j hj => ?_⟩
    have sj := slot_lt j
    obtain ⟨r7, r15⟩ := bswq_rev hj
    refine ⟨?_, ?_⟩
    · refine (v L hL (7 - j) (by omega_arith)).trans ?_
      rw [r7, ite_eq_left sj, show slot j % 8 = slot j by omega_arith, slot_slot hj]
      show qI (isA j) (byte (pw s.mem B (plc p 1)) (8 * L + slot j) ^^^ kb s (56 + slot j)) ^^^
        kb s (64 + (7 - j)) = _
      rw [h1 L hL j hj, k56 j hj, xor4, h.key hf hi4 (by omega_arith), (hk.out j hj).1, AesNi.bz_xor]
      exact congrArg (· ^^^ _) (AesNi.qI_qT _ _)
    · refine (v L hL (15 - j) (by omega_arith)).trans ?_
      rw [r15, ite_eq_right (by omega_arith), show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj,
        Nat.add_sub_cancel]
      show qI (isA j) (byte (pw s.mem B (plc p 0)) (8 * L + slot j)) ^^^ kb s (64 + (15 - j)) = _
      rw [h0 L hL j hj, h.key hf hi4 (by omega_arith), show 64 + (15 - j) = 72 + (7 - j) by omega_arith,
        (hk.out j hj).2, AesNi.bz_xor]
      exact congrArg (· ^^^ _) (AesNi.qI_qT _ _)
  · rintro s' ⟨f, ⟨hm', v⟩, rfl⟩
    obtain ⟨r1, r2, fr⟩ := st2_mem s.mem B (f .xmm0) (f .xmm2)
      (show blk (2 * p) + 16 = blk (2 * p + 1) by unfold blk; omega_arith) (by omega_arith)
    refine ⟨⟨f, _, rfl⟩, hm', fr, fun L hL j hj => ?_⟩
    rcases two hL with rfl | rfl
    · rw [show blk (2 * p + 0) = blk (2 * p) from rfl, r1]; exact v 0 (by decide) j hj
    · rw [r2]; exact v 1 (by decide) j hj

open VG.Proof.Camellia (pair group groups byteOf)

/-- The 32 bytes of a pair's blocks are among the places and the blocks. -/
theorem sub_blocks {p : Nat} (hp : p < 2) {m m' : Mem}
    (h : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p)), 32⟩] m m') :
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by unfold blk; omega_arith) (by unfold blk; omega_arith)⟩

/-- A block's bytes in memory, from their halves' in the block's order. -/
theorem out_bytes {m : Mem} {b : Nat} {x y : BitVec 64}
    (key : ∀ j < 8, byte (pw m B (blk b)) (7 - j) = bz y j ∧ byte (pw m B (blk b)) (15 - j) = bz x j) :
    ∀ q < 16, m (B.setWidth 64 + BitVec.ofNat 64 (blk b + q)) = if q < 8 then byteOf y q else byteOf x (q - 8) :=
  fun q hq => by
    rw [← byte_pw m B (blk b) hq]
    by_cases h8 : q < 8
    · have := (key (7 - q) (by omega_arith)).1
      rw [show 7 - (7 - q) = q by omega_arith] at this
      rw [ite_eq_left h8, this, AesNi.bz_byteOf _ (by omega_arith), show 7 - (7 - q) = q by omega_arith]
    · have := (key (15 - q) (by omega_arith)).2
      rw [show 15 - (15 - q) = q by omega_arith] at this
      rw [ite_eq_right h8, this, AesNi.bz_byteOf _ (by omega_arith), show 7 - (15 - q) = q - 8 by omega_arith]

/-- The places after the last round to the four blocks, a pair at a time. -/
theorem refOut_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hg1 : 1 ≤ g) (hg : g ≤ 4) (h : WAt s₀ B (g - 1) s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {P : Nat → BitVec 64 × BitVec 64}
    (ht : TriAt s.mem B (E (2 + 8 * (g - 1) + 5)) P) :
    WP isa (.block refOut) s (Part s fun m =>
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem m ∧
      ∀ b < 4, ∀ q < 16, m (B.setWidth 64 + BitVec.ofNat 64 (blk b + q)) =
        if q < 8 then byteOf ((P b).2 ^^^ E (8 * g)) q else byteOf ((P b).1 ^^^ E (8 * g + 1)) (q - 8)) := by
  refine WP.block_append_iff.mpr (WP.mono (pairOut_wp (p := 0) (by decide) hs hk hg1 hg h hm
    (a := fun L => (P (2 * 0 + L)).1) (b := fun L => (P (2 * 0 + L)).2) (ht 0 (by decide)).1 (ht 0 (by decide)).2)
    fun s₁ ⟨e₁, m₁, F₁, x₁⟩ => ?_)
  have a₁ := h.part e₁ (sub_blocks (by decide) F₁)
  have q0 : pw s₁.mem B (plc 1 0) = pw s.mem B (plc 1 0) := pw_frame F₁ (.inl (by decide)) (by decide) (by decide)
  have q1 : pw s₁.mem B (plc 1 1) = pw s.mem B (plc 1 1) := pw_frame F₁ (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (pairOut_wp (p := 1) (by decide) hs hk hg1 hg a₁ m₁
    (a := fun L => (P (2 * 1 + L)).1) (b := fun L => (P (2 * 1 + L)).2) (by rw [q0]; exact (ht 1 (by decide)).1)
    (by rw [q1]; exact (ht 1 (by decide)).2)) fun s₂ ⟨e₂, m₂, F₂, x₂⟩ => ?_
  refine ⟨xm_trans e₁ e₂, m₂, (sub_blocks (by decide) F₁).trans (sub_blocks (by decide) F₂),
    fun b hb q hq => ?_⟩
  have hb' : b = 2 * 0 + 0 ∨ b = 2 * 0 + 1 ∨ b = 2 * 1 + 0 ∨ b = 2 * 1 + 1 := by omega_arith
  rcases hb' with rfl | rfl | rfl | rfl
  · rw [byte_frame F₂ (.inl (by unfold blk; omega_using [hq])) (by decide) (by unfold blk; omega_using [hq])]
    exact out_bytes (x₁ 0 (by decide)) q hq
  · rw [byte_frame F₂ (.inl (by unfold blk; omega_using [hq])) (by decide) (by unfold blk; omega_using [hq])]
    exact out_bytes (x₁ 1 (by decide)) q hq
  · exact out_bytes (x₂ 0 (by decide)) q hq
  · exact out_bytes (x₂ 1 (by decide)) q hq

end

/-! ### The block function -/

section
variable {s₀ s : State} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64}

open VG.Proof.Camellia (pair group groups byteOf)

/-- The four blocks of the scratch buffer to the first round's halves in
the places: `cryptHead` reads the blocks, the keys, and the two stack
arguments. -/
theorem cryptHead_wp {R : Nat} (hB : s.gpr sb = B) (hs : Scr s B) (hR : R = 18 ∨ R = 24)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) :
    WP isa (.block cryptHead) s fun s' => WAt s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (R / 6) ∧
      ∀ p < 2, ∀ L < 2, ∀ r < 8,
        byte (pw s'.mem B (plc p 0)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq r))) ^^^
            kAt s.mem B r ∧
        byte (pw s'.mem B (plc p 1)) (8 * L + r) =
          qT (isA (slot r)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk (2 * p + L) + bswq (r + 8)))) ^^^
            kAt s.mem B (8 + r) := by
  have hf := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.mov tbr (.mem ⟨sb, 0⟩) :: .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) ::
    .shift .shr .ecx 3 :: .alu .add .ecx (.imm 1) :: .mov kr (.reg sb) :: .alu .add kr (.imm 24) ::
    ([tb m0 wM0] ++ wIn))) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_ldm (u₁.other .esp (by decide)) (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ => ?_
  refine Wp.wp_shr (by decide) fun s₃ u₃ _ => ?_
  refine Wp.wp_addi fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have a : WAt s B 0 s₆ := by
    refine ⟨?_, ?_, by rw [e₆]; exact Frame.refl _ _, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms],
      ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hB]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, addr_eq (by omega_arith), BitVec.add_zero]
      exact htab
    · rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hB]
      rfl
  have hn := a.krNat hf (by decide)
  refine WP.block_append_iff.mpr (WP.mono (m0_wp (by rw [a.tb, a.syms]) (by omega_arith) fun o ho =>
    ⟨_, List.mem_append_right _ (by rw [a.wr]; exact hs.wr), by
      rw [a.adr hf (by decide) (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) fun s₇ ⟨e₇, m₇⟩ => ?_)
  have a₇ : WAt s B 0 s₇ := by
    obtain ⟨f, rfl⟩ := e₇
    exact ⟨a.base, a.esp, a.frame, a.rd, a.wr, a.syms, a.tb, a.kp⟩
  have em : s₇.mem = s.mem := by obtain ⟨f, rfl⟩ := e₇; exact e₆
  have ec : s₇.gpr .ecx = s₆.gpr .ecx := by obtain ⟨f, rfl⟩ := e₇; rfl
  refine WP.mono (transfer in_equiv (a₇.pre hs (by decide)) (refIn_wp hs a₇ m₇)) fun s' ⟨e', hm', F', x'⟩ => ?_
  refine ⟨a₇.part e' F', hm', ?_, fun p hp L hL r hr => ?_⟩
  · have : s'.gpr .ecx = s₇.gpr .ecx := by obtain ⟨f, m, rfl⟩ := e'; rfl
    rw [this, ec, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
    show (s.mem.readW (s.ea (argOp 1)) 32 >>> 3) + 1 = _
    rw [hv]
    rcases hR with rfl | rfl <;> rfl
  · have := x' p hp L hL r hr
    rw [em] at this
    exact this

/-- The loop's invariant, with `n` groups left. -/
def Inv (s₀ : State) (B : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (d₀ : Nat → BitVec 64 × BitVec 64) (n : Nat)
    (s : State) : Prop :=
  1 ≤ n ∧ n ≤ g ∧ WAt s₀ B (g - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧
    HalvesAt s.mem B E (g - n) (fun b => (List.range (g - n)).foldl (group g E) (d₀ b))

/-- The groups of rounds: the halves after the last, in the places. -/
theorem loop_wp (hs : Scr s₀ B) (hk : Keys s₀.mem B g E) (hg : g ≤ 4) {d₀ : Nat → BitVec 64 × BitVec 64} {n : Nat}
    (hI : Inv s₀ B g E d₀ n s) :
    WP isa (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne) s fun s' =>
      WAt s₀ B (g - 1) s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      TriAt s'.mem B (E (2 + 8 * (g - 1) + 5)) (fun b => groups g E (d₀ b)) := by
  refine WP.loop (M := isa) (Inv s₀ B g E d₀) ?_ n s hI
  rintro n s ⟨hn, hng, a, hm, hc, hh⟩
  refine WP.seq (WP.mono (rounds_wp hs hk (by omega_arith) hg a hm hh hc hn (by omega_arith))
    fun s₁ ⟨a₁, m₁, c₁, z₁, t₁⟩ => ?_)
  refine WP.ite (decide (n = 1)) z₁ (fun hb => WP.block_nil (.inl ⟨?_, ?_⟩)) fun hb => ?_
  · show s₁.zf.map _ = _
    rw [z₁, hb]; rfl
  · have h1 : n = 1 := of_decide_eq_true hb
    subst h1
    have e : (fun b => groups g E (d₀ b)) =
        fun b => AesNi.tri E (g - 1) ((List.range (g - 1)).foldl (group g E) (d₀ b)) := funext fun b => by
      have := AesNi.foldl_group g E (d₀ b) (g - 1)
      rw [Nat.sub_add_cancel hng] at this
      rw [groups, this, AesNi.group_eq, ite_eq_right (by omega_arith)]
    rw [e]
    exact ⟨a₁, m₁, t₁⟩
  · have h1 : n ≠ 1 := of_decide_eq_false hb
    have hi : g - n + 1 < g := by omega_arith
    refine WP.mono (layer_wp hs hk hi hg a₁ m₁ t₁ c₁ (by omega_arith) (by omega_arith))
      fun s₂ ⟨a₂, m₂, c₂, z₂, h₂⟩ => .inr ⟨?_, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_, m₂, c₂, ?_⟩
    · show s₂.zf.map _ = _
      rw [z₂]; rfl
    · rw [show g - (n - 1) = g - n + 1 by omega_arith]; exact a₂
    · rw [show g - (n - 1) = g - n + 1 by omega_arith]
      have e : (fun b => (List.range (g - n + 1)).foldl (group g E) (d₀ b)) = fun b =>
          (Spec.Camellia.fl (AesNi.tri E (g - n) ((List.range (g - n)).foldl (group g E) (d₀ b))).1
              (E (8 + 8 * (g - n))),
            Spec.Camellia.flinv (AesNi.tri E (g - n) ((List.range (g - n)).foldl (group g E) (d₀ b))).2
              (E (9 + 8 * (g - n)))) := funext fun b => by
        rw [AesNi.foldl_group, AesNi.group_eq, ite_eq_left hi]
      rw [e]
      exact h₂

/-- `crypt` enciphers the four blocks at byte 576 of the scratch buffer,
each under the keys there, and changes nothing else in memory but the
places. -/
theorem crypt_wp {R : Nat} (hB : s.gpr sb = B) (hs : Scr s B) (hR : R = 18 ∨ R = 24)
    (hk : Keys s.mem B (R / 6) E) (hin : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) :
    WP isa crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩] s.mem s'.mem ∧
      ∀ b < 4, Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b)) 16 =
        (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6) E (Spec.Camellia.decodeBlock
          (Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b)))))).toList := by
  obtain ⟨g, hg⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg34 : g = 3 ∨ g = 4 := by omega_arith
  rw [hg] at hk ⊢
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Nat → BitVec 64, D₁ = fun b => (Spec.Camellia.decodeBlock
    (Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b))) >>> 64).setWidth 64 := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : Nat → BitVec 64, D₂ = fun b => (Spec.Camellia.decodeBlock
    (Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b)))).setWidth 64 := ⟨_, rfl⟩
  have hb : ∀ b, ∀ j < 8, s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b + (7 - j))) = bz (D₁ b) j ∧
      s.mem (B.setWidth 64 + BitVec.ofNat 64 (blk b + (15 - j))) = bz (D₂ b) j := fun b j hj => by
    rw [AesNi.bz_byteOf _ hj, AesNi.bz_byteOf _ hj, hD₁, hD₂]
    show _ = byteOf ((Spec.Camellia.decodeBlock _ >>> 64).setWidth 64) _ ∧
      _ = byteOf ((Spec.Camellia.decodeBlock _).setWidth 64) _
    rw [Proof.Camellia.byteOf_hi _ (by omega_arith), Proof.Camellia.byteOf_lo _ (by omega_arith),
      AesNi.blockAt_get _ _ (by omega_arith), AesNi.blockAt_get _ _ (by omega_arith),
      Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
      show blk b + (8 + (7 - j)) = blk b + (15 - j) by omega_arith]
    exact ⟨rfl, rfl⟩
  show WP isa (.seq (.block cryptHead) (.seq (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne)
    (.block wOut))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs hR hin hv htab) fun s₁ ⟨a₁, m₁, c₁, x₁⟩ => ?_)
  have hI : Inv s B g E (fun b => (D₁ b ^^^ E 0, D₂ b ^^^ E 1)) g s₁ := by
    refine ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact a₁, m₁, by rw [c₁, hg], ?_⟩
    rw [Nat.sub_self]
    intro p hp
    refine ⟨fun L hL j hj => ?_, fun L hL j hj => ?_⟩
    · have sj := slot_lt j
      show byte (pw s₁.mem B (plc p 0)) (8 * L + slot j) = dq (D₁ (2 * p + L) ^^^ E 0) j ^^^ dq (E 2) j ^^^ c5
      rw [(x₁ p hp L hL (slot j) sj).1, slot_slot hj, (AesNi.bswq_slot hj).1, (hk.kin0 j hj).1, (hb _ j hj).1,
        dq_xor, dq_xor]
      simp only [dq, BitVec.xor_assoc]
    · have sj := slot_lt j
      show byte (pw s₁.mem B (plc p 1)) (8 * L + slot j) =
        dq (D₂ (2 * p + L) ^^^ E 1) j ^^^ dq (E 3) j ^^^ c5 ^^^ gc j
      rw [(x₁ p hp L hL (slot j) sj).2, slot_slot hj, (AesNi.bswq_slot hj).2, Nat.add_comm 8 (slot j),
        (hk.kin0 j hj).2, (hb _ j hj).2, dq_xor, dq_xor]
      simp only [dq, BitVec.xor_assoc]
  refine WP.seq (WP.mono (loop_wp hs hk (by omega_arith) hI) fun s₂ ⟨a₂, m₂, t₂⟩ => ?_)
  refine WP.mono (transfer out_equiv (a₂.pre hs (by omega_arith))
    (refOut_wp hs hk (by omega_arith) (by omega_arith) a₂ m₂ t₂)) fun s₃ ⟨e₃, _, F₃, v₃⟩ => ?_
  have a₃ := a₂.part e₃ F₃
  refine ⟨a₃.base, a₃.esp, a₃.rd, a₃.wr, a₃.syms, a₃.frame, fun b hb4 => ?_⟩
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
  have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  subst hD₁ hD₂
  rw [Vector.getElem_toList]
  simp only [Proof.Camellia.cryptWords]
  rw [Proof.Camellia.encodeBlock_getElem _ _ hq, ← v₃ b hb4 q hq]
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat]

end

end

/-! ## The keys `prepare` leaves -/

section

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNiWide
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 x ld stx)
open VG.Impl.Camellia.X86 (Dir)
open VG.Impl.Modes.X86 (sb at_ argOp)
open VG.Proof.Camellia.X86.AesNi (slot dq gc c5 bswq bz slot_lt slot_slot kAt wAt Keys Sch Ew PEnv PAt X6)
open VG.Proof.Camellia (decPerm)

variable {s : State} {B : BitVec 32}

/-- The subkeys `E` in `d`'s order, for `g` groups of rounds. -/
def Ed : Dir → Nat → (Nat → BitVec 64) → Nat → BitVec 64
  | .encrypt, _, E => E
  | .decrypt, g, E => fun k => E (decPerm g k)

theorem decPerm_lt {g k : Nat} (hg : g = 3 ∨ g = 4) (hk : k < 8 * g + 2) : decPerm g k < 34 := by
  unfold decPerm
  split <;> [skip; split] <;> omega_arith

/-- A subkey, from its eight bytes. -/
theorem wordAt_bytes {m m' : Mem} {a a' : Addr}
    (h : ∀ i < 8, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    Spec.Camellia.wordAt m' a' = Spec.Camellia.wordAt m a := by
  simp only [Spec.Camellia.wordAt, Spec.Camellia.bytesAt]
  congr 1
  exact List.map_congr_left fun i hi => h i (by simpa using hi)

/-- A copy of the schedule: what `copyOk` says of it, of a state. -/
theorem copy_wp {c : List Instr} {n : Nat} {src : Nat → Nat} {sw : Nat → Bool} (hok : copyOk c n src sw = true)
    {p : BitVec 32} (hB : s.gpr sb = B) (hax : s.gpr .eax = p)
    (htb : s.gpr tbr = s.syms Impl.Camellia.X86.AesNi.tableName)
    (hs : Scr s B) (hsch : (⟨p.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr) (hpf : p.toNat + 272 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 856⟩) :
    WP isa (.block c) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 544, 272⟩] s.mem s'.mem ∧
      ∀ u < n, ∀ q < 16, s'.mem (B.setWidth 64 + BitVec.ofNat 64 (544 + 16 * u + q)) =
        s.mem (p.setWidth 64 + BitVec.ofNat 64 (16 * src u + (if sw u = true then (q + 8) % 16 else q))) := by
  have hf := hs.fit
  unfold copyOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  rw [Bool.and_eq_true] at hok
  obtain ⟨hin, hall⟩ := hok
  have hrel : Rel cparams (envOf cparams s) Regs.init s := rel_init (p := cparams) htb
    (by show (s.gpr .eax).toNat + 272 ≤ _; rw [hax]; exact hpf)
    fun o ho => ⟨_, hsch, by
      show Region.Contains _ (addr (s.gpr .eax) o) 16
      have ho' : o + 16 ≤ 272 := ho
      rw [hax, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ok : OutOk cparams coparams s := ⟨by show (s.gpr sb).toNat + 816 ≤ _; rw [hB]; omega_arith,
    fun o ho => ⟨_, hs.wr, by
      show Region.Contains _ (addr (s.gpr sb) o) 16
      have ho' : o + 16 ≤ 816 := ho
      rw [hB, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    by
      show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 272⟩ ⟨(s.gpr sb).setWidth 64, 816⟩
      rw [hax, hB]; exact hsep.sub_right (Region.sub_prefix (by decide)),
    by show (s.gpr .eax).toNat + 272 ≤ _; rw [hax]; exact hpf⟩
  refine runS_wp ok (RelS.init hrel rfl) hrun fun s' hr =>
    ⟨hr.gpr, hr.rd, hr.wr, hr.syms, ?_, fun u hu q hq => ?_⟩
  · have := hr.frameIn hin
    rw [show s.gpr coparams.oreg = s.gpr sb from rfl, hB] at this
    exact this
  · have hu' := List.all_eq_true.mp hall u (List.mem_range.mpr hu)
    rw [Bool.and_eq_true] at hu'
    have hsrc : src u ≤ 16 := of_decide_eq_true hu'.1
    have := hr.out hu'.2 hq
    rw [show s.gpr coparams.oreg = s.gpr sb from rfl, hB] at this
    rw [this, BV.var_eval _ (by show 128 + _ < 1024; split <;> omega_arith), envOf_key,
      show s.gpr cparams.kreg = s.gpr .eax from rfl, hax]

/-- The subkeys of the copy at byte 544 of the scratch buffer. -/
theorem copy_words {m m' : Mem} {p : BitVec 32} {n : Nat} {src : Nat → Nat} {sw : Nat → Bool}
    (hf : B.toNat + 856 ≤ 2 ^ 32)
    (h : ∀ u < n, ∀ q < 16, m' (B.setWidth 64 + BitVec.ofNat 64 (544 + 16 * u + q)) =
      m (p.setWidth 64 + BitVec.ofNat 64 (16 * src u + (if sw u = true then (q + 8) % 16 else q))))
    {k : Nat} (hk : k < 2 * n) :
    Ew m' (B + BitVec.ofNat 32 544) k =
      Ew m p (2 * src (k / 2) + (if sw (k / 2) = true then 1 - k % 2 else k % 2)) := by
  unfold Ew
  rw [show (B + BitVec.ofNat 32 544).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 544 from
    addr_eq (by omega_arith)]
  refine wordAt_bytes fun i hi => ?_
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]
  have := h (k / 2) (by omega_arith) (8 * (k % 2) + i) (by omega_arith)
  rw [show 544 + (8 * k + i) = 544 + 16 * (k / 2) + (8 * (k % 2) + i) by omega_arith, this]
  by_cases hw : sw (k / 2) = true
  · rw [ite_eq_left hw, ite_eq_left hw]
    exact congrArg (fun z => m (p.setWidth 64 + BitVec.ofNat 64 z)) (by omega_arith)
  · rw [ite_eq_right hw, ite_eq_right hw]
    exact congrArg (fun z => m (p.setWidth 64 + BitVec.ofNat 64 z)) (by omega_arith)

/-- The schedule's copy holds its subkeys in `d`'s order. -/
theorem prepCopy_wp {d : Dir} {p : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4) (hB : s.gpr sb = B)
    (hax : s.gpr .eax = p) (htb : s.gpr tbr = s.syms Impl.Camellia.X86.AesNi.tableName)
    (hc : s.gpr .ecx = BitVec.ofNat 32 g)
    (hs : Scr s B) (hsch : (⟨p.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr) (hpf : p.toNat + 272 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 856⟩) :
    WP isa (prepCopy d) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 544, 272⟩] s.mem s'.mem ∧
      ∀ k < 8 * g + 2, Ew s'.mem (B + BitVec.ofNat 32 544) k = Ed d g (Ew s.mem p) k := by
  have hf := hs.fit
  cases d
  · refine WP.mono (copy_wp copy_all.1 hB hax htb hs hsch hpf hsep) fun s' ⟨eg, er, ew, es, F, h⟩ =>
      ⟨eg, er, ew, es, F, fun k hk => ?_⟩
    rw [copy_words hf h (by omega_arith)]
    exact congrArg (Ew s.mem p) (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith)
  · show WP isa (.seq (.block [.alu .cmp .ecx (.imm 3)]) (.ite .e (.block (copyDec 3)) (.block (copyDec 4)))) s _
    refine WP.seq (Wp.wp_cmpi fun s₁ u₁ _ z₁ => WP.block_nil ?_)
    have z : s₁.zf = some (decide (g = 3)) := by
      rw [z₁, hc, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
    have hs₁ : Scr s₁ B := ⟨by rw [u₁.wr]; exact hs.wr, hs.fit⟩
    refine WP.ite (decide (g = 3)) z (fun hb => ?_) fun hb => ?_
    · have h3 : g = 3 := of_decide_eq_true hb
      subst h3
      refine WP.mono (copy_wp copy_all.2.1 (by rw [u₁.gpr]; exact hB) (by rw [u₁.gpr]; exact hax)
        (by rw [u₁.gpr, u₁.syms]; exact htb) hs₁ (by rw [u₁.rd, u₁.wr]; exact hsch) hpf hsep)
        fun s' ⟨eg, er, ew, es, F, h⟩ => ⟨eg.trans u₁.gpr, er.trans u₁.rd, ew.trans u₁.wr, es.trans u₁.syms,
          by rw [← u₁.mem]; exact F, fun k hk => ?_⟩
      rw [copy_words hf h (by omega_arith), u₁.mem]
      have := List.all_eq_true.mp perm_all.1 k (List.mem_range.mpr hk)
      rw [beq_iff_eq] at this
      exact congrArg (Ew s.mem p) this
    · have h4 : g = 4 := by have : g ≠ 3 := of_decide_eq_false hb; omega_arith
      subst h4
      refine WP.mono (copy_wp copy_all.2.2 (by rw [u₁.gpr]; exact hB) (by rw [u₁.gpr]; exact hax)
        (by rw [u₁.gpr, u₁.syms]; exact htb) hs₁ (by rw [u₁.rd, u₁.wr]; exact hsch) hpf hsep)
        fun s' ⟨eg, er, ew, es, F, h⟩ => ⟨eg.trans u₁.gpr, er.trans u₁.rd, ew.trans u₁.wr, es.trans u₁.syms,
          by rw [← u₁.mem]; exact F, fun k hk => ?_⟩
      rw [copy_words hf h (by omega_arith), u₁.mem]
      have := List.all_eq_true.mp perm_all.2 k (List.mem_range.mpr hk)
      rw [beq_iff_eq] at this
      exact congrArg (Ew s.mem p) this

/-- The schedule's pointer to the copy, and the copy's first two subkeys
in the rounds' form: in a state `AesNi.prepare`'s loop starts in. -/
theorem prepStart_wp {p : BitVec 32} {M : Mem} (hB : s.gpr sb = B) (he : PEnv s B p)
    (hp : p = B + BitVec.ofNat 32 544) (htb : s.gpr tbr = s.syms Impl.Camellia.X86.AesNi.tableName)
    (hkr : s.gpr kr = B + BitVec.ofNat 32 (24 + 112 * 0)) (hS : Sch M s.mem p) :
    WP isa (.block prepStart) s fun s' => PAt s B p 0 s' ∧ s'.gpr .ecx = s.gpr .ecx ∧ s'.mem = s.mem ∧
      X6 (s'.xmm .xmm6) (Ew M p) 0 := by
  have hpf := he.pfit
  show WP isa (.block (.mov .eax (.reg sb) :: .alu .add .eax (.imm 544) :: Impl.Camellia.X86.AesNi.prepHeadX)) s _
  refine Wp.wp_mov fun s₁ u₁ => ?_
  refine Wp.wp_addi fun s₂ u₂ => ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have r₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  have w₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  have y₂ : s₂.syms = s.syms := by rw [u₂.syms, u₁.syms]
  have b₂ : s₂.gpr sb = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have sp₂ : s₂.gpr .esp = s.gpr .esp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have t₂ : s₂.gpr tbr = s.syms Impl.Camellia.X86.AesNi.tableName := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), htb]
  have a₂ : s₂.gpr .eax = p := by rw [u₂.gpr, u₁.gpr, hB, hp]; rfl
  have c₂ : s₂.gpr .ecx = s.gpr .ecx := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have k₂ : s₂.gpr kr = B + BitVec.ofNat 32 (24 + 112 * 0) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hkr]
  have hS₂ : Sch M s₂.mem p := by rw [m₂]; exact hS
  have hok := AesNi.prep_all.1
  unfold AesNi.prepHeadOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨x6s, x6⟩, mk⟩ := hok
  have hrel : Rel AesNi.pparams (envOf AesNi.pparams s₂) Regs.init s₂ := rel_init (p := AesNi.pparams)
    (by show s₂.gpr tbr = s₂.syms Impl.Camellia.X86.AesNi.tableName; rw [t₂, y₂])
    (by show (s₂.gpr .eax).toNat + 80 ≤ _; rw [a₂]; omega_arith)
    fun o ho => ⟨_, by rw [r₂, w₂]; exact he.sch, by
      show Region.Contains _ (addr (s₂.gpr .eax) o) 16
      have ho' : o + 16 ≤ 80 := ho
      rw [a₂, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine run_wp hrel hrun fun s' hr hs => ?_
  obtain ⟨f, rfl⟩ := hs
  refine ⟨⟨b₂, sp₂, r₂, w₂, y₂, t₂, by rw [show (_ : State).gpr .eax = s₂.gpr .eax from rfl, a₂]; simp, k₂,
    AesNi.rel_mask hr mk⟩, c₂, m₂, ?_⟩
  rw [X6, ite_eq_left rfl]
  intro j hj
  have sj := slot_lt j
  rw [AesNi.rel_bytes hr x6s x6 (show slot j < 16 by omega_arith),
    AesNi.rel_bytes hr x6s x6 (show slot j + 8 < 16 by omega_arith),
    AesNi.pT_eval 0 (by omega_arith) (by decide), AesNi.pT_eval 0 (by omega_arith) (by decide),
    (AesNi.bswq_slot hj).1, (AesNi.bswq_slot hj).2, show slot j % 8 = slot j by omega_arith,
    show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj, a₂,
    show 0 + (7 - j) = 8 * 0 + (7 - j) by omega_arith, show 0 + (15 - j) = 8 * 1 + (7 - j) by omega_arith,
    AesNi.sch_bz hS₂ (by decide) hj, AesNi.sch_bz hS₂ (by decide) hj]
  exact ⟨rfl, rfl⟩

/-- The keys of the copy: `AesNi.prepare`'s loop and tail, in a state with
that code's scratch buffer. -/
theorem prepKeys_wp {p : BitVec 32} {M : Mem} {g : Nat} (hB : s.gpr sb = B) (he : PEnv s B p)
    (hp : p = B + BitVec.ofNat 32 544) (htb : s.gpr tbr = s.syms Impl.Camellia.X86.AesNi.tableName)
    (hkr : s.gpr kr = B + BitVec.ofNat 32 (24 + 112 * 0)) (hc : s.gpr .ecx = BitVec.ofNat 32 g)
    (hg : g = 3 ∨ g = 4) (hS : Sch M s.mem p) :
    WP isa (.seq (.block prepStart) (.seq (.loop (.seq (.block Impl.Camellia.X86.AesNi.prepGroup)
      (.ite .e (.block []) (.block Impl.Camellia.X86.AesNi.prepMasks))) .ne)
      (.block Impl.Camellia.X86.AesNi.prepTail))) s fun s' =>
      Keys s'.mem B g (Ew M p) ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] s.mem s'.mem := by
  refine WP.seq (WP.mono (prepStart_wp hB he hp htb hkr hS) fun s₂ ⟨a₂, c₂, e₂, x₂⟩ => ?_)
  have hI : AesNi.PInv s M s₂.mem B p g g s₂ :=
    ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact a₂, by rw [c₂, hc], by rw [e₂]; exact hS,
      Frame.refl _ _, by rw [Nat.sub_self]; exact AesNi.KeysTo.zero _ _ _ _, by rw [Nat.sub_self]; exact x₂⟩
  refine WP.seq (WP.mono (AesNi.ploop_wp he (by omega_arith) hI) fun s₃ ⟨a₃, hS₃, F₃, K₃⟩ => ?_)
  refine WP.mono (AesNi.prepTail_wp he (i := g - 1) (by omega_arith) a₃ hS₃ (k := 8 * g) (by omega_arith))
    fun s₄ ⟨a₄, f₄, o₄⟩ => ?_
  rw [Nat.add_assoc] at f₄
  have K₄ := K₃.frame f₄ (by omega_arith) (fun i' h' => by omega_arith) (fun i' h' _ => by omega_arith)
    (by omega_arith)
  refine ⟨⟨K₄.kin0 (by omega_arith), K₄.kin, K₄.rk, K₄.rk4, K₄.rk5, fun i hi => K₄.fl i hi (by omega_arith), o₄⟩,
    a₄.base, a₄.esp, a₄.syms, ?_⟩
  rw [e₂] at F₃
  exact F₃.trans (f₄.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)

/-- This file's table's address to the scratch buffer's first slot,
`AesNi.table`'s to its register, and the schedule, the groups and the keys'
pointer from the stack arguments. -/
theorem prepHead_wp {R : Nat} {p : BitVec 32} (hB : s.gpr sb = B) (hs : Scr s B) (hR : R = 18 ∨ R = 24)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 856⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨B.setWidth 64, 856⟩) :
    WP isa (.block prepHead) s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧ s'.gpr tbr = s.gpr .eax ∧ s'.gpr .eax = p ∧
      s'.gpr .ecx = BitVec.ofNat 32 (R / 6) ∧ s'.gpr kr = B + BitVec.ofNat 32 (24 + 112 * 0) ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.gpr kr := by
  have hf := hs.fit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨sb, 0⟩ kr :: .mov tbr (.reg .eax) :: .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) ::
    .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) :: .shift .shr .ecx 3 :: .alu .add .ecx (.imm 1) ::
    .mov kr (.reg sb) :: [.alu .add kr (.imm 24)])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 856⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  have e1 : s₂.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1B.sub_right sub4) (by decide), hv]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0) fun s₄ u₄ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin1) fun s₅ u₅ => ?_
  refine Wp.wp_shr (by decide) fun s₆ u₆ _ => ?_
  refine Wp.wp_addi fun s₇ u₇ => ?_
  refine Wp.wp_mov fun s₈ u₈ => ?_
  refine Wp.wp_addi fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₂.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨?_, ?_, by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr],
    by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms], ?_, ?_, ?_, ?_,
    by rw [m₉]; exact f₂, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.mem, u₃.mem]
    show (s₂.mem.readW (s.ea (argOp 1)) 32 >>> 3) + 1 = _
    rw [e1]
    rcases hR with rfl | rfl <;> rfl
  · rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
    rfl
  · rw [m₉, u₂.mem, ha0, Mem.readW_writeW_self32]

/-- `prepare d` leaves the keys of the schedule's subkeys, in `d`'s order,
in the scratch buffer, and the table's address in its first slot; it writes
only the core's slots, and the four bytes below `esp` of the frames that
get the tables' addresses. -/
theorem prepare_wp {d : Dir} {R : Nat} {p : BitVec 32} (hB : s.gpr sb = B) (hs : Scr s B)
    (hR : R = 18 ∨ R = 24) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 856⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨B.setWidth 64, 856⟩)
    (hsch : (⟨p.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr) (hpf : p.toNat + 272 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 856⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 272⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩)
    (h1S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 1), 4⟩) :
    WP isa (prepare d) s fun s' => Keys s'.mem B (R / 6) (Ed d (R / 6) (Ew s.mem p)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 816⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  obtain ⟨g, hg⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg34 : g = 3 ∨ g = 4 := by omega_arith
  have hf := hs.fit
  rw [hg]
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq
    (.block [.mov kr (.reg .eax)]) (.seq
    (.frame (.symPush .eax Impl.Camellia.X86.AesNi.tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead)
    (.seq (prepCopy d) (.seq (.block prepStart) (.seq (.loop (.seq (.block Impl.Camellia.X86.AesNi.prepGroup)
      (.ite .e (.block []) (.block Impl.Camellia.X86.AesNi.prepMasks))) .ne)
      (.block Impl.Camellia.X86.AesNi.prepTail)))))))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  refine WP.seq (Wp.wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [u₂.other _ (by decide)]; exact esp₁
  refine WP.seq (WP.mono (symFrame_ok Impl.Camellia.X86.AesNi.tableName s₂ (by rw [esp₂]; exact hesp))
    fun s₃ a₃ => ?_)
  have esp₃ : s₃.gpr .esp = s.gpr .esp := (a₃.gpr .esp (by decide)).trans esp₂
  have F₃ : Frame [below (s.gpr .esp) 4] s.mem s₃.mem := by
    have f3 := a₃.frame
    rw [esp₂, u₂.mem] at f3
    exact a₁.frame.trans f3
  have ea₃ : ∀ k, s₃.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₃.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₃]
  have rd₃ : s₃.rd = s.rd := a₃.rd.trans (u₂.rd.trans a₁.rd)
  have wr₃ : s₃.wr = s.wr := a₃.wr.trans (u₂.wr.trans a₁.wr)
  have sy₃ : s₃.syms = s.syms := a₃.syms.trans (u₂.syms.trans a₁.syms)
  have B₃ : s₃.gpr sb = B := by rw [a₃.gpr _ (by decide), u₂.other _ (by decide), a₁.gpr _ (by decide)]; exact hB
  have p₃ : s₃.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [F₃.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  have v₃ : s₃.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [F₃.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1S.symm) (by decide), hv]
  have k₃ : s₃.gpr kr = s.syms tableName := by rw [a₃.gpr _ (by decide), u₂.gpr, a₁.addr]
  have x₃ : s₃.gpr .eax = s.syms Impl.Camellia.X86.AesNi.tableName := by rw [a₃.addr, u₂.syms, a₁.syms]
  refine WP.seq (WP.mono (prepHead_wp (R := R) (p := p) B₃ ⟨by rw [wr₃]; exact hs.wr, hf⟩ hR
    (by rw [ea₃, rd₃, wr₃]; exact hin0) (by rw [ea₃]; exact p₃) (by rw [ea₃]; exact h0B)
    (by rw [ea₃, rd₃, wr₃]; exact hin1) (by rw [ea₃]; exact v₃) (by rw [ea₃]; exact h1B))
    fun s₄ ⟨B₄, esp₄, rd₄, wr₄, sy₄, t₄, x₄, c₄, k₄, F₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (prepCopy_wp (d := d) (p := p) hg34 B₄ x₄ (by rw [t₄, x₃, sy₄, sy₃]) (by rw [c₄, hg])
    ⟨by rw [wr₄, wr₃]; exact hs.wr, hf⟩ (by rw [rd₄, wr₄, rd₃, wr₃]; exact hsch) hpf hsep)
    fun s₅ ⟨g₅, rd₅, wr₅, sy₅, F₅, w₅⟩ => ?_)
  obtain ⟨p', hp'⟩ : ∃ p' : BitVec 32, p' = B + BitVec.ofNat 32 544 := ⟨_, rfl⟩
  have p64 : p'.setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 544 := by rw [hp']; exact addr_eq (by omega_arith)
  have pn : p'.toNat = B.toNat + 544 := by
    rw [hp', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 544) (by decide), Nat.mod_eq_of_lt (by omega_arith)]
  have hsw : (⟨B.setWidth 64, 856⟩ : Region) ∈ s₅.wr := by rw [wr₅, wr₄, wr₃]; exact hs.wr
  have cov : Covers [⟨p'.setWidth 64, 272⟩, ⟨B.setWidth 64, 544⟩] s₅.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hsw, 544, p64, by show (544 : Nat) + 272 ≤ 856; decide⟩
    · exact ⟨_, hsw, 0, (BitVec.add_zero _).symm, by show (0 : Nat) + 544 ≤ 856; decide⟩
  have ew : ∀ j < 34, Ew s₄.mem p j = Ew s.mem p j := fun j hj => by
    unfold Ew
    rw [Proof.Camellia.wordAt_frame F₄ fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide)),
      Proof.Camellia.wordAt_frame F₃ fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact hkS.symm.sub_left (Offset.sub_base _ (by omega_arith))]
  refine WP.narrow (rd := [⟨p'.setWidth 64, 272⟩]) (wr := [⟨B.setWidth 64, 544⟩])
    (P := fun t => Keys t.mem B g (Ew s₅.mem p') ∧ t.gpr sb = B ∧ t.gpr .esp = s₅.gpr .esp ∧ t.syms = s₅.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] s₅.mem t.mem)
    (prepKeys_wp (s := s₅.withRegions [⟨p'.setWidth 64, 272⟩] [⟨B.setWidth 64, 544⟩]) (M := s₅.mem)
      (by show s₅.gpr sb = B; rw [g₅]; exact B₄)
      ⟨⟨List.mem_singleton_self _, by omega_arith⟩, List.mem_cons_self, by omega_arith, by
        rw [p64]; exact Offset.disjoint_base _ (Nat.le_refl _) (by decide)⟩
      hp' (by show s₅.gpr tbr = s₅.syms _; rw [g₅, t₄, x₃, sy₅, sy₄, sy₃])
      (by show s₅.gpr kr = _; rw [g₅]; exact k₄) (by show s₅.gpr .ecx = _; rw [g₅, c₄, hg]) hg34
      (fun o _ => rfl))
    (Covers.right cov) (Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, hsw, 0, (BitVec.add_zero _).symm, by show (0 : Nat) + 544 ≤ 856; decide⟩)
    (fun s₆ rd₆ wr₆ F₆ ⟨K, b₆, e₆, sy₆, G₆⟩ => ?_) (by lit_decide)
  have K : Keys s₆.mem B g (Ew s₅.mem p') := K
  have G₆ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] s₅.mem s₆.mem := G₆
  refine ⟨K.congr (by omega_arith) fun k hk => ?_, ?_, b₆, ?_, by rw [rd₆, rd₅, rd₄, rd₃],
    by rw [wr₆, wr₅, wr₄, wr₃], ?_, ?_⟩
  · rw [hp', w₅ k hk]
    cases d
    · exact ew k (by omega_arith)
    · exact ew _ (decPerm_lt hg34 hk)
  · rw [G₆.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide),
      F₅.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), r₄, k₃]
  · exact e₆.trans (by rw [g₅, esp₄, esp₃])
  · exact sy₆.trans (by rw [sy₅, sy₄, sy₃])
  · refine (((F₃.mono fun r hr => ?_).trans (F₄.sub fun r hr => ?_)).trans (F₅.sub fun r hr => ?_)).trans
      (F₆.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩

end

/-! ## The core -/

section

open VG VG.X86 VG.Impl.Camellia.X86.AesNiWide
open VG.Impl.Camellia.X86 (Dir)
open VG.Impl.Modes.X86 (sb at_ argOp)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Camellia (schedWords schedWords_getD decPerm)
open VG.Proof.Camellia.X86.AesNi (Keys Ew kAt wAt)

/-- The key `k` is ready, for the direction `d`, in the scratch buffer at
`B`: its keys in `d`'s order, the table's address in the first slot, and
the number of rounds still in its stack argument. -/
def Ready (d : Dir) (s : State) (B : BitVec 32) (k : Nat × List (BitVec 64)) : Prop :=
  Keys s.mem B (k.1 / 6) (Ed d (k.1 / 6) fun i => k.2.getD i 0) ∧
    s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ AesNi.RArg s k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    B.toNat + 856 ≤ 2 ^ 32

theorem decPerm_lt' {g k : Nat} (hk : k < 8 * g + 2) : decPerm g k < 8 * g + 2 := by
  unfold decPerm
  split <;> [skip; split] <;> omega_arith

/-- The cipher of the direction `d`, on a block in memory. -/
theorem dir_bytes {d : Dir} {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : Mem) (p : Addr) :
    dirCipher d (Spec.Camellia.subkeysOfWords R ws) (Spec.Aes.bytesAt m p 16) =
      (Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6) (Ed d (R / 6) fun i => ws.getD i 0)
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)))).toList := by
  cases d
  · exact Proof.Camellia.cipher_bytes hR ws m p
  · show Spec.Camellia.invCipher _ _ = _
    rw [Spec.Camellia.invCipher, Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.ofFn_toList,
      Spec.Camellia.decryptBlock, Proof.Camellia.decryptWith_eq hR]
    rfl

/-- The key stays ready through writes apart from the first 504 bytes of the
scratch buffer. -/
theorem ready_keep {d : Dir} {s s' : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r')
    (keep : ∀ {a n : Nat}, a + n ≤ 504 → ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r) :
    Ready d s' B k := by
  obtain ⟨hk, ht, ha, hR, hfit⟩ := h
  refine ⟨hk.eqOn (by omega_arith) fun o ho => ?_, ?_, ha.frame hesp hrd hwr hf hs, hR, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (24 + o), 1⟩) (keep (by omega_arith))
      (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    exact this
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide)) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

/-- The key stays ready through what a mode writes outside the core's slots
or within its buffer. -/
theorem ready_frame {d : Dir} {s s' : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core d) B) r ∨ Region.Sub r (blkRegion (core d) B)) :
    Ready d s' B k :=
  ready_keep h hesp hrd hwr hsy hf hs fun {a n} h₁ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by show a + n ≤ 4 * 204; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * 144) (k := 4 * 4 * 4)
        (by omega_arith) (by omega_arith) (by decide)).sub_right h

theorem prepare_ok {d : Dir} {s : State} {B : BitVec 32} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total)
    (hR : (⟨B.setWidth 64, 4 * (core d).total⟩ : Region) ∈ rs) (hk : AesNi.KeyArgs s rs k)
    (hsp : (core d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (core d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hkS, h0S, h1S⟩ := hk
  simp only at hRa hRv hws ⊢
  refine WP.mono (prepare_wp (d := d) hB hs hRv hsp hin0 hp (hd0 _ hR) hin1 hRa (hd1 _ hR) hsch hfit (hdis _ hR)
    hkS h0S h1S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨K.congr (by omega_arith) fun i hi => ?_, by rw [t, sy], ⟨by rw [rd, wr, AesNi.ea_esp e]; exact hin1, ?_,
    by rw [wr, AesNi.ea_esp e]; exact hdw⟩, hRv, hs.fit⟩, b, e, f, rd, wr⟩
  · cases d
    · show Ew s.mem p i = ws.getD i 0
      rw [hws, schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact hi)]
      rfl
    · show Ew s.mem p (decPerm (R / 6) i) = ws.getD (decPerm (R / 6) i) 0
      rw [hws, schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact decPerm_lt' hi)]
      rfl
  · rw [AesNi.ea_esp e, f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hRa]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hd1 _ hR).sub_right (Region.sub_prefix (by show 816 ≤ 4 * 214; decide))
    · exact h1S.symm

theorem crypt_ok {d : Dir} {s : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : VG.Proof.Modes.X86.ScrIn s B (core d).total) (hr : Ready d s B k) :
    WP isa (core d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready d s' B k ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧
      (∀ j < (core d).G, Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) (4 * (core d).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) (4 * (core d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hk, ht, ha, hR, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs hR hk ha.1 ha.2.1 ht) fun s' ⟨b, e, rd, wr, sy, f, v⟩ => ?_
  have hblk : ∀ j, blkAddr (core d) B j = B.setWidth 64 + BitVec.ofNat 64 (blk j) := fun j => by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 144) + BitVec.ofNat 64 (4 * 4 * j) = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun z => B.setWidth 64 + BitVec.ofNat 64 z) (by unfold blk; omega_arith)
  have hsub : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 512, 128⟩ : Region)], ∃ r' ∈ s.wr, Region.Sub r r' :=
    fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, hs.wr, Offset.sub_base _ (by show 512 + 128 ≤ 4 * 214; decide)⟩
  refine ⟨b, e, ready_keep ⟨hk, ht, ha, hR, hfit⟩ e rd wr sy f hsub (fun {a n} h₁ r hr => ?_),
    f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by decide)
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 512 + 128 ≤ 4 * 204; decide)⟩
  · show Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) 16 =
      dirCipher d _ (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) 16)
    rw [hblk, dir_bytes hR]
    exact v j hj

/-- Camellia's core of four blocks by the AES S-box meets what the modes
need, in the direction `d`. -/
def coreSpec (d : Dir) : CoreSpec (core d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := AesNi.KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, core]
  layout := ⟨by show 0 < 4; decide, .inr rfl, by show 144 + 4 * 4 ≤ 204; decide, by show 204 + 10 ≤ 214; decide⟩
  keyArgs_congr h e r w _ f := AesNi.keyArgs_congr h e r w f
  ready_frame h e r w sy f hs hd := ready_frame h e r w sy f hs hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Camellia.X86.AesNiWide
