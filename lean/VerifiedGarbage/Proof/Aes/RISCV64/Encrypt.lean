module

public import VerifiedGarbage.Proof.Aes.RISCV64.Layers
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Framework.RISCV64.Align

/-!
# Encrypting four blocks, bitsliced, on RISC-V

As on x86-64 (`Proof/Aes/X86_64/Encrypt.lean`): `encrypt4_ok`, from four
blocks in the registers (`InRel`), with the bitsliced round keys and the
masks in the scratch buffer (`EncPre`), `encrypt4` leaves the four
ciphertexts, having written only the first 320 bytes of the scratch buffer.
The layers are composed from their proofs (`Layers.lean`); the round loop's
invariant is the specification's `foldl` over the rounds done.

The scratch buffer of 2048 bytes at `X` is used from `X` rounded up to a
multiple of 8 (`Scr`), which leaves room for its 255 slots.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.Bitslice VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)

/-! ## The scratch buffer -/

/-- The scratch buffer: `N` writable bytes at `X`, `a5` at `X` rounded up
to a multiple of 8. -/
structure Scr (s : State) (X : Addr) (N : Nat) : Prop where
  wr : (⟨X, N⟩ : Region) ∈ s.wr
  base : s.gpr sb = X + BitVec.ofNat 64 (pad X)

theorem Scr.congr {s s' : State} {X : Addr} {N : Nat} (h : Scr s X N) (hwr : s'.wr = s.wr)
    (hsb : s'.gpr sb = s.gpr sb) : Scr s' X N := ⟨hwr ▸ h.wr, hsb.trans h.base⟩

theorem Scr.al {s : State} {X : Addr} {N : Nat} (h : Scr s X N) : (s.gpr sb).toNat % 8 = 0 := by
  rw [h.base]; exact align_al X

/-- Bytes `d … d + n` from the rounded base are in the buffer. -/
theorem Scr.contains {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {d n : Nat}
    (hd : d + n + 7 ≤ N) (hN : N < 2 ^ 63) :
    (⟨X, N⟩ : Region).Contains (s.gpr sb + BitVec.ofNat 64 d) n := by
  rw [h.base, Offset.add_add]
  have := pad_lt X
  exact Offset.contains_base X (by omega) (by omega)

/-- Bytes `d … d + n` from the rounded base are a part of the buffer. -/
theorem Scr.sub {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {d n : Nat} (hd : d + n + 7 ≤ N) :
    Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 d, n⟩ ⟨X, N⟩ := by
  rw [h.base, Offset.add_add]
  have := pad_lt X
  exact Offset.sub_base X (by omega)

/-- `Ok` for the slots from `a5` on, and no external words. -/
theorem Scr.okSlots {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {c : Cfg} (hb : c.base = sb)
    (he : c.ext = sb) (hx : c.exts = 0) (hn : 8 * c.slots + 7 ≤ N) (hN : N < 2 ^ 63) : Ok c s where
  slotIn k hk := ⟨_, h.wr, by rw [hb]; exact h.contains (by omega) hN⟩
  extIn k hk := by omega
  baseAl _ := by rw [hb]; exact h.al
  extAl _ := by rw [he]; exact h.al
  slots := by omega
  sep k _ j hj := by omega

/-- `Ok` for the external words from `a5` on, and no slots. -/
theorem Scr.okExts {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {c : Cfg} (hb : c.base = sb)
    (he : c.ext = sb) (hx : c.slots = 0) (hn : 8 * c.exts + 7 ≤ N) (hN : N < 2 ^ 63) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := ⟨_, List.mem_append_right _ h.wr, by rw [he]; exact h.contains (by omega) hN⟩
  baseAl _ := by rw [hb]; exact h.al
  extAl _ := by rw [he]; exact h.al
  slots := by omega
  sep k hk := by omega

/-! ## What encryption needs and keeps -/

/-- All the masks. -/
def allKs : List (Nat × BitVec 64) := bsKs ++ srKs ++ invSrKs

theorem allKs_slots : ∀ p ∈ allKs, 40 ≤ p.1 ∧ p.1 < 76 := by decide

theorem masksAt_sub {m : Mem} {b : Addr} {ks ks' : List (Nat × BitVec 64)} (h : MasksAt m b ks)
    (hs : ∀ p ∈ ks', p ∈ ks) : MasksAt m b ks' := fun k v hk => h k v (hs _ hk)

/-- The bitsliced round keys `0 … R` of the schedule `w`, from `K0`, 64 bytes each. -/
def KeysAt (m : Mem) (K0 : Addr) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (wordAddr (K0 + BitVec.ofNat 64 (64 * j)) k) 64) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `X`) is
writable, the masks are in it, and the round keys, the last at byte
`lastKey` from `a5`, with the first at `a0`. -/
structure EncPre (s₀ : State) (X : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : Scr s₀ X 2048
  masks : MasksAt s₀.mem (s₀.gpr sb) allKs
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  k0 : s₀.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (1920 - 64 * R)
  keys : KeysAt s₀.mem (s₀.gpr .a0) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 320⟩] s₀.mem s.mem

theorem sb_not : sb ∉ sboxWrites ∧ sb ≠ kp := by decide
theorem a0_not : Reg.a0 ∉ sboxWrites ∧ Reg.a0 ≠ kp := by decide

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ sb_not.1 sb_not.2

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [⟨s.gpr sb, 320⟩] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

theorem Ctx.scr {s₀ s : State} {X : Addr} {N : Nat} (h : Scr s₀ X N) (hc : Ctx s₀ s) : Scr s X N :=
  h.congr hc.wr hc.base

/-- A slot at or above 40 is outside the first 320 bytes. -/
theorem slot_kept {m m' : Mem} {b : Addr} (h : Frame [⟨b, 320⟩] m m') {k : Nat} (hk : 40 ≤ k)
    (hk' : k < 256) : m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  h.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains])
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base b (by omega) (by omega)) (by decide)

theorem Ctx.masks {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) allKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) allKs := by
  intro k v hk
  have := allKs_slots _ hk
  rw [hc.base, slot_kept hc.frame this.1 (by omega)]
  exact hm k v hk

theorem Ctx.sboxOk {s₀ s : State} {X : Addr} (h : Scr s₀ X 2048) (hc : Ctx s₀ s) : Ok sboxCfg s :=
  (hc.scr h).okSlots rfl rfl rfl (by decide) (by decide)

theorem Ctx.bsOk {s₀ s : State} {X : Addr} (h : Scr s₀ X 2048) (hc : Ctx s₀ s) : Ok bsCfg s :=
  (hc.scr h).okExts rfl rfl rfl (by decide) (by decide)

theorem Ctx.srOk {s₀ s : State} {X : Addr} (h : Scr s₀ X 2048) (hc : Ctx s₀ s) : Ok srCfg s :=
  (hc.scr h).okExts rfl rfl rfl (by decide) (by decide)

theorem Ctx.bsKs {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) allKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) bsKs :=
  masksAt_sub (hc.masks hm) fun p hp => by simp only [allKs, List.mem_append]; exact .inl (.inl hp)

theorem Ctx.srKs {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) allKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) srKs :=
  masksAt_sub (hc.masks hm) fun p hp => by simp only [allKs, List.mem_append]; exact .inl (.inr hp)

theorem Ctx.invSrKs {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) allKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) invSrKs :=
  masksAt_sub (hc.masks hm) fun p hp => by simp only [allKs, List.mem_append]; exact .inr hp

/-- The key area is outside what the layers write. -/
theorem keys_disjoint (b : Addr) : Region.Disjoint ⟨b + 1024, 960⟩ ⟨b, 320⟩ :=
  Offset.disjoint_base (d := 1024) b (by omega_arith) (by omega_arith)

theorem addr3 (b : Addr) (x y z : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y + BitVec.ofNat 64 z = b + BitVec.ofNat 64 (x + y + z) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]

theorem key_contains (b : Addr) {R j k : Nat} (hR : R ≤ 14) (hj : j ≤ R) (hk : k < 8) :
    (⟨b + 1024, 960⟩ : Region).Contains
      (wordAddr (b + BitVec.ofNat 64 (1920 - 64 * R) + BitVec.ofNat 64 (64 * j)) k) (64 / 8) := by
  simp only [wordAddr]
  rw [addr3]
  exact Offset.contains (e := 1024) b (by omega_arith) (by omega_arith) (by omega_arith)

theorem keyRel_congr {K K' : Nat → BitVec 64} {rk : List Byte} (h : KeyRel K rk)
    (he : ∀ k < 8, K' k = K k) : KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

theorem EncPre.keysAt {s₀ s : State} {X : Addr} {R : Nat} {w : List Byte} (hp : EncPre s₀ X R w)
    (hc : Ctx s₀ s) : KeysAt s.mem (s₀.gpr .a0) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (key_contains _ hR hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact keys_disjoint _) (by decide)

theorem ark_cfg_ok {s : State} {X : Addr} (hs : Scr s X 2048) {n : Nat}
    (hk : s.gpr kp = s.gpr sb + BitVec.ofNat 64 n) (hn : n + 64 ≤ 2040) (h8 : n % 8 = 0) :
    Ok arkCfg s where
  slotIn k hk := by simp [arkCfg] at hk
  extIn k hk' := by
    simp only [arkCfg] at hk'
    refine ⟨⟨X, 2048⟩, List.mem_append_right _ hs.wr, ?_⟩
    show (⟨X, 2048⟩ : Region).Contains (wordAddr (s.gpr kp) k) 8
    rw [wordAddr, hk, Offset.add_add]
    exact hs.contains (by omega) (by decide)
  baseAl _ := hs.al
  extAl _ := by
    show (s.gpr kp).toNat % 8 = 0
    rw [hk, hs.base]
    exact align_al_add X h8
  slots := by simp [arkCfg]
  sep k hk := by simp [arkCfg] at hk

/-! ## One layer at a time -/

/-- A layer that writes only the state registers, the temporaries and (at
most) the first 320 bytes of the scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {c : Cfg} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ Rest c s s') (hcb : c.base = sb)
    (hcs : c.slots ≤ 40) (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hsp, hoth, hfr⟩ := hl
  refine WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr hsp (fun r h _ => hoth r h) ?_) hP
    (hoth kp (by decide))⟩
  refine hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, fun a ha => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, hcb, Region.Contains] at ha ⊢
  omega

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    midRounds w (m + 1) x = rnd w (m + 1) (midRounds w m x) := by
  simp [midRounds, List.range_succ, List.foldl_append]

theorem kp_step (K : Addr) (m : Nat) :
    K + BitVec.ofNat 64 (64 * m) + BitVec.ofNat 64 64 = K + BitVec.ofNat 64 (64 * (m + 1)) := by
  rw [Offset.add_add, show 64 * m + 64 = 64 * (m + 1) by omega_arith]

theorem q_ne_kp (i : Nat) : q i ≠ kp := by
  unfold q; split <;> decide

theorem q_ne_t0 (i : Nat) : q i ≠ t0 := by
  unfold q; split <;> decide

/-- `addi kp, kp, 64`. -/
theorem addKp_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 →
      (∀ i, Proof.Aes.RISCV64.Q s' i = Proof.Aes.RISCV64.Q s i) → Q s') :
    WP isa (.block [.addi kp kp 64]) s Q := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write]
  · intro i; simp [Proof.Aes.RISCV64.Q, State.write, q_ne_kp i]

/-- `sub t0, kp, a5; addi t0, t0, -(lastKey - 64)`. -/
theorem cmpLast_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp →
      (∀ i, Proof.Aes.RISCV64.Q s' i = Proof.Aes.RISCV64.Q s i) →
      s'.gpr t0 = s.gpr kp - s.gpr sb - BitVec.ofNat 64 (lastKey - 64) → Q s') :
    WP isa (.block [.sub t0 kp sb, .addi t0 t0 (-((lastKey - 64 : Nat) : Int))]) s Q := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_sub, runStep_some, runBlock_cons,
    exec_addi (by decide), runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [State.write, this]) (Frame.refl _ _)
  · simp [State.write, t0, kp]
  · intro i; simp [Proof.Aes.RISCV64.Q, State.write, q_ne_t0 i]
  · simp only [State.write, t0, kp, sb, ite_true, lastKey]
    rw [BitVec.sub_eq_add_neg (s.gpr _ - _)]
    rfl

theorem zf_last (b : Addr) {R m : Nat} (hR : R ≤ 14) (hm : m + 1 < R) :
    (b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (lastKey - 64) == 0) =
      decide (m + 2 = R) := by
  rw [Offset.add_sub_cancel_left]
  by_cases h : m + 2 = R
  · subst h
    rw [show 1920 - 64 * (m + 2) + 64 * (m + 1) = lastKey - 64 by simp only [lastKey]; omega_arith]
    simp
  · have hne : BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - BitVec.ofNat 64 (lastKey - 64) ≠ 0 := by
      intro h'
      apply h
      simp only [lastKey] at h'
      bv_omega
    simpa [h] using hne

theorem kp_off (K0 b : Addr) {R j : Nat} (hk : K0 = b + BitVec.ofNat 64 (1920 - 64 * R)) :
    K0 + BitVec.ofNat 64 (64 * j) = b + BitVec.ofNat 64 (1920 - 64 * R + 64 * j) := by
  rw [hk, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ark_step {s₀ s : State} {X : Addr} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ X R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * j))
    (hj : j ≤ R) (hbs : BsRel (Q s) T) {P : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp →
      BsRel (Q s') (fun b => addRoundKey (T b) (roundKey w j)) → P s') :
    WP isa (.block addRoundKey) s P := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hok : Ok arkCfg s := ark_cfg_ok (hc.scr hp.scr)
    (by rw [hk, kp_off _ _ hp.k0, hc.base]) (by omega_arith) (by omega_arith)
  have hkey : KeyRel (keyWord s) (roundKey w j) := by
    have := hp.keysAt hc j hj
    unfold keyWord; rw [hk]; exact this
  obtain ⟨s', hs', h', hr⟩ := addRoundKey_ok hok
  refine layer_wp ⟨s', hs', h', hr⟩ rfl (by decide) hc fun s₁ hc₁ h₁ hk₁ =>
    h s₁ hc₁ hk₁ (bs_addRoundKey h₁ hbs hkey)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {X : Addr} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ X R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * m))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block roundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * (m + 1)) ∧
      BsRel (Q s') (fun b => rnd w (m + 1) (T b)) ∧ (s'.gpr t0 == 0) = decide (m + 2 = R) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_step] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (sbox_ok (hc₁.sboxOk hp.scr)) rfl (by decide) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine layer_wp (shiftRows_ok (hc₂.srOk hp.scr) (hc₂.srKs hp.masks)) rfl (by decide) hc₂
    fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine layer_wp (mixColumns_ok (hc₃.bsOk hp.scr)) rfl (by decide) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * (m + 1)) := by rw [hk₄, hk₃, hk₂, hk₁]
  refine ark_step hp hc₄ hk₄' (by omega_arith) hbs₄ fun s₅ hc₅ hk₅ hbs₅ => ?_
  refine cmpLast_wp hc₅ fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅, hk₄']
  · have : Q s₆ = Q s₅ := funext hq₆
    rw [this]; exact hbs₅
  · rw [hz₆, hk₅, hk₄', hc₅.base, kp_off _ _ hp.k0, zf_last _ hR hm]

theorem eval_t0 {s : State} {b : Bool} (h : (s.gpr t0 == 0) = b) :
    isa.eval (.nonzero t0) s = some (!b) := by
  simp [RISCV64.eval, ← h, bne]

/-- `mv kp, a0`. -/
theorem movKp_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr .a0 →
      (∀ i, Proof.Aes.RISCV64.Q s' i = Proof.Aes.RISCV64.Q s i) → Q s') :
    WP isa (.block [movR kp .a0]) s Q := by
  refine WP.of_runBlock ⟨_, by rw [movR, runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write]
  · intro i; simp [Proof.Aes.RISCV64.Q, State.write, q_ne_kp i]

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Four blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt4_ok {s₀ : State} {X : Addr} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ X R w) (hin : InRel (Q s₀) S) :
    WP isa encrypt4 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => cipher R w (S b)) := by
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega_arith
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * m) ∧ BsRel (Q s) (fun b => midRounds w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * (R - 1)) ∧
    BsRel (Q s) (fun b => midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok ((Ctx.refl s₀).bsOk hp.scr) ((Ctx.refl s₀).bsKs hp.masks)) rfl
      (by decide) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine movKp_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by
      have : Q s₂ = Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .a0 + BitVec.ofNat 64 (64 * 0) := by
      rw [hk₂, hc₁.keep _ a0_not.1 a0_not.2]; simp
    exact ark_step hp hc₂ hk₂' (by omega_arith) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega_arith, by omega_arith, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simpa [hlast] using eval_t0 hz, hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega_arith
      · rw [show R - 1 = m + 1 by omega_arith]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨by simpa [hlast] using eval_t0 hz, R - 1 - (m + 1), by omega_arith, m + 1, rfl,
        by omega_arith, hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, kp_step, show R - 1 + 1 = R by omega_arith] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => midRounds w (R - 1) (A b)) := by
      have : Q s₁ = Q s := funext hq₁
      rw [this]; exact hbs
    refine layer_wp (sbox_ok (hc₁.sboxOk hp.scr)) rfl (by decide) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine layer_wp (shiftRows_ok (hc₂.srOk hp.scr) (hc₂.srKs hp.masks)) rfl (by decide) hc₂
      fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok (hc₄.bsOk hp.scr) (hc₄.bsKs hp.masks)) rfl (by decide) hc₄
      fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [cipher_eq]; rfl

end VG.Proof.Aes.RISCV64
