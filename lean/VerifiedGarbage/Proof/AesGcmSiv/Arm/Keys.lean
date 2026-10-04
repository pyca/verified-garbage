import VerifiedGarbage.Proof.AesGcmSiv.Arm.Derive
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Gcm.Arm.Ghash

/-!
# AES-GCM-SIV on ARMv7: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 192` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Proof.AesGcm.Arm (KeyCall KeyPost key_call below add_ofNat_zero add_ofNat_assoc covers_cons covers_nil
  covers_append' ofNat_sub32 mem_store gpr_store sp_store rd_store wr_store z_store)

/-! ## Blocks stored a word at a time -/

/-- A block stored as four words, read by GHASH. -/
theorem blockAt_store4 (m : Mem) (p : Addr) (a b c d : BitVec 32) :
    Spec.Gcm.blockAt (Proof.Cmac.store4 m p a b c d) p = Proof.Gcm.Arm.w4 (rev a) (rev b) (rev c) (rev d) := by
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨p + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint p h (by omega) (by omega)
  have d₀ : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by
    simpa using dj (x := 0) (y := 4) (.inl (by decide)) (by decide) (by decide)
  have d₀' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by
    simpa using dj (x := 0) (y := 8) (.inl (by decide)) (by decide) (by decide)
  have d₀'' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by
    simpa using dj (x := 0) (y := 12) (.inl (by decide)) (by decide) (by decide)
  rw [Proof.Gcm.Arm.blockAt_rev, Proof.Cmac.store4]
  simp only [Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ d₀.symm, Proof.Cmac.readW_writeW_disj _ d₀'.symm,
    Proof.Cmac.readW_writeW_disj _ d₀''.symm, Mem.readW_writeW_self32]

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 192`. -/
structure ExpPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩, ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩]
    t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 32 R - BitVec.ofNat 32 6) <<< 2 = BitVec.ofNat 32 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub32 (by omega) (by omega), ofNat_lsl32]
  congr 1; unfold Spec.GcmSiv.keyLen; omega

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa expandArgs t = some t₁ ∧
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 1712)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ ∧ t₁.mem = t.mem := by
  have hl : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h] <;> decide
  have hR := L.rounds
  have ww := L.ww
  refine ⟨_, by simp only [expandArgs]; srun [E.r8, E.r11], ⟨?r0, ?r1, ?r2, ?r3, ?len, ?fK, ?fC, ?fS, ?kc, ?ks, ?cs,
    ?rd, ?wr⟩, E.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by rfl⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E.r11]
  case r1 => simp [gpr_setReg, E.r8, keyLen_lsl hR]
  case r2 => simp [gpr_setReg, E.r11]
  case r3 => simp [gpr_setReg, E.r11]
  case len => omega
  case fK => rw [L.wN (by decide)]; omega
  case fC => rw [L.wN (by decide)]; omega
  case fS => rw [L.wN (by decide)]; omega
  case kc => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case ks => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case cs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case rd => rw [L.wA (by decide)]; exact E.perm.wCR (by omega)
  case wr =>
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

theorem expand_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) : WP isa expand t (ExpPost p t) := by
  obtain ⟨t₁, run₁, kc, E₁, hm₁⟩ := expArgs_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call kc) fun t₂ P => ?_
  have fr := P.frame
  have out := P.out
  simp only [L.wA (show 32 < 3760 by decide), L.wA (show 192 < 3760 by decide),
    L.wA (show 1712 < 3760 by decide)] at fr out
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [← hm₁]; exact fr, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `w₀`–`w₃` of the authentication key, as
`hkey` computes it: its four words, the most significant first. -/
abbrev hk3 (w₀ w₃ : BitVec 32) : BitVec 32 := (w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)
abbrev hkW (lo hi : BitVec 32) : BitVec 32 := (lo >>> 1) ||| (hi <<< 31)

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let w₀ := m.readW (W + BitVec.ofNat 64 16) 32
  let w₁ := m.readW (W + BitVec.ofNat 64 20) 32
  let w₂ := m.readW (W + BitVec.ofNat 64 24) 32
  let w₃ := m.readW (W + BitVec.ofNat 64 28) 32
  Proof.Cmac.zero4 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 64) (rev (hk3 w₀ w₃)) (rev (hkW w₂ w₃))
    (rev (hkW w₁ w₂)) (rev (hkW w₀ w₁))) (W + BitVec.ofNat 64 80)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩).trans
    ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩)

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  rw [hkeyMem, Proof.Cmac.zero4, Proof.AesGcm.Arm.blockAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.hkeyOf_words,
    GcmSiv.Words32.ofBytes_bytesAt, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [hkeyMem, Proof.Cmac.zero4, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_zero]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = hkeyMem t.mem (State.addr p.W) ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 16 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 20 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 24 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 28 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 64 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 68 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 72 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 76 + 4 ≤ 3760 by decide)
  have w₄ := E.perm.wW (show 80 + 4 ≤ 3760 by decide)
  have w₅ := E.perm.wW (show 84 + 4 ≤ 3760 by decide)
  have w₆ := E.perm.wW (show 88 + 4 ≤ 3760 by decide)
  have w₇ := E.perm.wW (show 92 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [hkey, Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, w₄,
    w₅, w₆, w₇], ?_, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, hkeyMem, Proof.Cmac.zero4,
    Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule, the working spaces and the
stack below `SP`. -/
abbrev keyR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 192, 3568⟩, below SP]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : Prm) (σ t : State) : Prop where
  env : Env p t
  frame : Frame (keyR (State.addr p.W) p.SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem (State.addr p.N) 12)).1 = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
      (bytesAt σ.mem (State.addr p.N) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) : WP isa keys σ (KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (derive_ok L E) fun t₂ I => ?_)
  have k0 : (⟨State.addr p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR (State.addr p.W) p.SP := List.mem_cons_self
  have k1 : (⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region) ∈ keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨State.addr p.W + BitVec.ofNat 64 192, 3568⟩ : Region) ∈ keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have k3 : below p.SP ∈ keyR (State.addr p.W) p.SP := by simp
  have f₂ : Frame (keyR (State.addr p.W) p.SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k3, fun _ h => h⟩
  refine WP.seq (WP.mono (expand_ok L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ho₄, sp₄, rd₄, wr₄⟩ := hkey_ok L X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (keyR (State.addr p.W) p.SP) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
  have f₄ : Frame (keyR (State.addr p.W) p.SP) t₃.mem t₄.mem := by
    rw [hm₄]; exact (hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.AesGcm.Arm.bytesAt_frame (hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine WP.of_runBlock ⟨t₄, run₄, X.env.of_others ho₄ sp₄ rd₄ wr₄, (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.AesGcm.Arm.bytesAt_frame (hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.Arm
