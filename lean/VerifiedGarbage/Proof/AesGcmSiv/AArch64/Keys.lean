import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash

/-!
# AES-GCM-SIV on AArch64: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 240` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Proof.AesGcm.AArch64 (KeyCall KeyPost key_call GcmImpl covers_cons covers_nil covers_append
  ofNat_sub add_ofNat_assoc Others)

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 240`. -/
structure ExpPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨p.W + BitVec.ofNat 64 240, 240⟩, ⟨p.W + BitVec.ofNat 64 1760, 512⟩] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 64 R - BitVec.ofNat 64 6) <<< 2 = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub (by omega) (by omega), ofNat_lsl]
  congr 1; unfold Spec.GcmSiv.keyLen; omega

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa expandArgs t = some t₁ ∧
      KeyCall t₁ (p.W + BitVec.ofNat 64 32) (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 1760)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ ∧ t₁.mem = t.mem := by
  have hl : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h] <;> decide
  have hl' := L.rounds
  refine ⟨_, by simp only [expandArgs]; grun [E.x19, E.x22], ⟨?x0, ?x1, ?x2, ?x3, ?len, ?kc, ?ks, ?cs, ?rd, ?wr⟩,
    E.keep (fun r hr => ?regs) ?sp ?rdE ?wrE, ?mem⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  case sp => rfl
  case rdE => rfl
  case wrE => rfl
  case mem => rfl
  case x0 => simp [gpr_write]
  case x1 => simp [gpr_write, keyLen_lsl hl']
  case x2 => simp [gpr_write]
  case x3 => simp [gpr_write]
  case len => omega
  case kc => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case ks => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case cs => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case rd =>
    exact covers_append (covers_cons (E.perm.wCR (by omega)) covers_nil)
      (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  case wr => exact covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

theorem expand_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (expand v.callees) t (ExpPost p t) := by
  obtain ⟨t₁, run₁, kc, E₁, hm₁⟩ := expArgs_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call v.key kc) fun t₂ P => ?_
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [← hm₁]; exact P.frame, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
  have out := P.out
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `lo` and `hi` of the authentication key, as
`hkey` computes it: its high half and its low half. -/
abbrev hkHi (hi lo : BitVec 64) : BitVec 64 := (hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))
abbrev hkLo (hi lo : BitVec 64) : BitVec 64 := (lo >>> 1) ||| (hi &&& 1#64).rotateRight 1

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let lo := m.readW (W + BitVec.ofNat 64 16) 64
  let hi := m.readW (W + BitVec.ofNat 64 24) 64
  (((m.writeW (W + BitVec.ofNat 64 64) (rev64 (hkHi hi lo))).writeW (W + BitVec.ofNat 64 72)
    (rev64 (hkLo hi lo))).writeW (W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 88)
    (0 : BitVec 64)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) := by
  have ct : ∀ e, 64 ≤ e → e + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 e) (64 / 8) :=
    fun e h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 64 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ct 72 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ct 80 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (ct 88 (by decide) (by decide))

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  have c₁ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 80) (64 / 8) :=
    contains_at0 _ (by decide) (by decide)
  have c₂ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 88) (64 / 8) :=
    Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  rw [hkeyMem, Proof.AesGcm.AArch64.blockAt_frame
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))]
  have e := Proof.Gcm.AArch64.blockAt_storeMem m (W + BitVec.ofNat 64 64)
    (hkHi (m.readW (W + BitVec.ofNat 64 24) 64) (m.readW (W + BitVec.ofNat 64 16) 64))
    (hkLo (m.readW (W + BitVec.ofNat 64 24) 64) (m.readW (W + BitVec.ofNat 64 16) 64))
  rw [Proof.Gcm.AArch64.storeMem, BitVec.add_zero, add_ofNat_assoc] at e
  rw [e, GcmSiv.Words.hkeyOf_words, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [hkeyMem, show W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = hkeyMem t.mem p.W ∧
      Others [.x9, .x10, .x11, .x12, .x13] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₁ := E.perm.wR (show 16 + 8 ≤ 3808 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 3808 by decide)
  have w₁ := E.perm.wW (show 64 + 8 ≤ 3808 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 3808 by decide)
  have w₃ := E.perm.wW (show 80 + 8 ≤ 3808 by decide)
  have w₄ := E.perm.wW (show 88 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [hkey, zero16]; grun [E.x19, r₁, r₂, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, hkeyMem, Mem.writeW, BitVec.setWidth_eq,
      read8_readW]
    rfl
  · others_tac
  all_goals rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 224, 16⟩, ⟨W + BitVec.ofNat 64 240, 3568⟩]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : Prm) (σ t : State) : Prop where
  env : Env p t
  frame : Frame (keyR p.W) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem p.N 12)).1 = bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R) (bytesAt σ.mem p.N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa (keys v.callees) σ (KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (derive_ok v L E) fun t₂ I => ?_)
  have k0 : (⟨p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR p.W := List.mem_cons_self
  have k1 : (⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region) ∈ keyR p.W := List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨p.W + BitVec.ofNat 64 240, 3568⟩ : Region) ∈ keyR p.W :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have f₂ : Frame (keyR p.W) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.mono (expand_ok v L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ho₄, sp₄, rd₄, wr₄⟩ := hkey_ok X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region),
      ⟨p.W + BitVec.ofNat 64 1760, 512⟩], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (keyR p.W) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub p.W (by decide) (by decide)⟩
  have f₄ : Frame (keyR p.W) t₃.mem t₄.mem := by
    rw [hm₄]; exact (hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (p.W + BitVec.ofNat 64 16) 16 = bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.AesGcm.AArch64.bytesAt_frame (hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine WP.of_runBlock ⟨t₄, run₄, X.env.keep (fun r hr => ho₄ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄,
    (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.AesGcm.AArch64.bytesAt_frame (hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.AArch64
