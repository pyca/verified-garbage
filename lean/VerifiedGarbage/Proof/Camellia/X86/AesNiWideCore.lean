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

end

end

end VG.Proof.Camellia.X86.AesNiWide
