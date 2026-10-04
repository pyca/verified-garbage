import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.AesGcm.X86.J0

/-!
# AES-GCM-SIV on x86: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 512` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq zero4_fold GcmImpl readW_writeW_off)

/-! ## Blocks stored a word at a time -/

/-- A block of GHASH as the four words in memory, each byte-reversed. -/
theorem blockAt_bswap (m : Mem) (p : Addr) (d : Nat) :
    Spec.Gcm.blockAt m (p + BitVec.ofNat 64 d) = bswap (m.readW (p + BitVec.ofNat 64 d) 32) ++
      bswap (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ bswap (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      bswap (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Spec.Gcm.blockAt, bytesAt_words, Proof.AesGcm.X86.ofBytes_le4]
  rfl

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 512`. -/
structure ExpPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = t.gpr .esi
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 2048, 512⟩, stk p] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem expand_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (expand v.callees) t (ExpPost p t) := by
  have hR := L.rounds
  have hRs := E.slots.rounds
  simp only [slotv_eq, roundsO] at hRs
  obtain ⟨t₁, run₁, eax, ecx, edx, ebp₁, esp₁, esi₁, rd₁, wr₁, hm₁⟩ : ∃ t₁, runBlock isa expandArgs t = some t₁ ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 32 ∧ t₁.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧
      t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.mem = t.mem := by
    refine ⟨_, by simp only [expandArgs]; grun [E.ebp, L.aW, E.perm.wR, hRs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · gregs [E.ebp]
    · gregs [hRs, keyLen_eq hR]
    · gregs [E.ebp]
    · gregs [E.ebp]
    · gregs [E.esp]
    · gregs []
    all_goals gmems []
  have E₁ : Env p t₁ := E.keep (by rw [ebp₁, E.ebp]) (by rw [esp₁, E.esp]) rd₁ wr₁ hm₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (callKey_ok v L E₁ eax ecx edx)
    fun t₂ P => ⟨P.env, by rw [P.rd, rd₁], by rw [P.wr, wr₁], by rw [P.saved _ (by decide), esi₁], ?_, ?_⟩
  · rw [← hm₁]; exact P.frame
  · have out := P.out
    have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
      unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
    rw [hr] at out
    rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `w₀`–`w₃` of the authentication key, as
`hkey` computes its four words, the most significant first. -/
abbrev hk3 (w₀ w₃ : BitVec 32) : BitVec 32 := (w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)
abbrev hkW (lo hi : BitVec 32) : BitVec 32 := (lo >>> 1) ||| (hi &&& 1#32).rotateRight 1

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let w₀ := m.readW (W + BitVec.ofNat 64 16) 32
  let w₁ := m.readW (W + BitVec.ofNat 64 20) 32
  let w₂ := m.readW (W + BitVec.ofNat 64 24) 32
  let w₃ := m.readW (W + BitVec.ofNat 64 28) 32
  Proof.Cmac.zero4 ((((m.writeW (W + BitVec.ofNat 64 76) (bswap (hkW w₀ w₁))).writeW (W + BitVec.ofNat 64 72)
    (bswap (hkW w₁ w₂))).writeW (W + BitVec.ofNat 64 68) (bswap (hkW w₂ w₃))).writeW (W + BitVec.ofNat 64 64)
    (bswap (hk3 w₀ w₃))) (W + BitVec.ofNat 64 80)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) := by
  have c : ∀ d, 64 ≤ d → d + 4 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d)
      (32 / 8) := fun d h₁ h₂ => Offset.contains W (by omega) (by omega) (by omega)
  have m₀ : (⟨W + BitVec.ofNat 64 64, 32⟩ : Region) ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)] :=
    List.mem_singleton_self _
  exact (((((Frame.refl _ _).writeW m₀ _ (c 76 (by decide) (by decide))).writeW m₀ _
    (c 72 (by decide) (by decide))).writeW m₀ _ (c 68 (by decide) (by decide))).writeW m₀ _
    (c 64 (by decide) (by decide))).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩)

theorem bswap_bswap (a : BitVec 32) : bswap (bswap a) = a := Proof.Cmac.byteRev32_byteRev32 a

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  rw [hkeyMem, Proof.Cmac.zero4, Proof.AesGcm.X86.blockAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)), blockAt_bswap]
  simp (disch := decide) only [Nat.reduceAdd, Mem.readW_writeW_self32, readW_writeW_off, bswap_bswap, hkW, hk3,
    ror_and1]
  rw [GcmSiv.Words32.hkeyOf_words, GcmSiv.Words32.ofBytes_bytesAt, add_ofNat_assoc, add_ofNat_assoc,
    add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [hkeyMem, Proof.Cmac.zero4, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_zero]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = hkeyMem t.mem (w64 p.W) ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hz := zero4_fold ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 76)
      (bswap (hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 16) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 20) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 72)
      (bswap (hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 20) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 24) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 68)
      (bswap (hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 24) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 28) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 64)
      (bswap (hk3 (t.mem.readW (w64 p.W + BitVec.ofNat 64 16) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 28) 32))))
    p.W 80
  simp only [Nat.reduceAdd] at hz
  refine ⟨_, by simp only [hkey, hkeyW, zero4]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hkeyMem, hz]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use and the index, the encryption key's schedule, the working
spaces and the stack below `SP`. -/
abbrev keyR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 112⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 512, 3584⟩, stk p]

theorem inMut_keyR (p : Prm) : InMut p (keyR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : Prm) (σ t : State) : Prop where
  env : Env p t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  esi : t.gpr .esi = σ.gpr .esi
  frame : Frame (keyR p) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem (w64 p.N) 12)).1 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
      (bytesAt σ.mem (w64 p.N) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa (keys v.callees) σ (KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (derive_ok v L E) fun t₂ I => ?_)
  have k0 : (⟨w64 p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR p := List.mem_cons_self
  have k1 : (⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region) ∈ keyR p := by simp
  have k2 : (⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region) ∈ keyR p := by simp
  have k3 : (⟨w64 p.W + BitVec.ofNat 64 512, 3584⟩ : Region) ∈ keyR p := by simp
  have k4 : stk p ∈ keyR p := by simp
  have f₂ : Frame (keyR p) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, fun _ h => h⟩
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k4, fun _ h => h⟩
  refine WP.seq (WP.mono (expand_ok v L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ebp₄, esp₄, esi₄, rd₄, wr₄⟩ := hkey_ok L X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region),
      ⟨w64 p.W + BitVec.ofNat 64 2048, 512⟩, stk p],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.bw' (by omega)).symm
  have f₃ : Frame (keyR p) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k4, fun _ h => h⟩
  have f₄' : Frame [⟨w64 p.W + BitVec.ofNat 64 64, 32⟩] t₃.mem t₄.mem := by rw [hm₄]; exact hkeyMem_frame _ _
  have f₄ : Frame (keyR p) t₃.mem t₄.mem := f₄'.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₄' (dH (by decide)) (by decide)
  have E₄ : Env p t₄ := X.env.mut L ebp₄ esp₄ rd₄ wr₄ (frame_toMut f₄ (inMut_keyR p))
  refine WP.of_runBlock ⟨t₄, run₄, E₄, by rw [rd₄, X.rd, I.rd], by rw [wr₄, X.wr, I.wr],
    by rw [esi₄, X.esi, I.esi], (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₄' (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.X86
