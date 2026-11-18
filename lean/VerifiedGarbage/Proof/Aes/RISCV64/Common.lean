module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Proof.Aes.RISCV64.Layers

/-! ### `Aes.RISCV64.Keys`, which this module and modules that import it used -/

section

/-! ### `Aes.RISCV64.Encrypt`, which this module and modules that import it used -/

section

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
  exact Offset.contains_base X (by omega_using [hd, this]) (by omega_using [hd, hN, this])

/-- Bytes `d … d + n` from the rounded base are a part of the buffer. -/
theorem Scr.sub {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {d n : Nat} (hd : d + n + 7 ≤ N) :
    Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 d, n⟩ ⟨X, N⟩ := by
  rw [h.base, Offset.add_add]
  have := pad_lt X
  exact Offset.sub_base X (by omega_using [hd, this])

/-- `Ok` for the slots from `a5` on, and no external words. -/
theorem Scr.okSlots {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {c : Cfg} (hb : c.base = sb)
    (he : c.ext = sb) (hx : c.exts = 0) (hn : 8 * c.slots + 7 ≤ N) (hN : N < 2 ^ 63) : Ok c s where
  slotIn k hk := ⟨_, h.wr, by rw [hb]; exact h.contains (by omega_using [hn, hk]) hN⟩
  extIn k hk := by omega
  baseAl _ := by rw [hb]; exact h.al
  extAl _ := by rw [he]; exact h.al
  slots := by omega_using [hn, hN]
  sep k _ j hj := by omega

/-- `Ok` for the external words from `a5` on, and no slots. -/
theorem Scr.okExts {s : State} {X : Addr} {N : Nat} (h : Scr s X N) {c : Cfg} (hb : c.base = sb)
    (he : c.ext = sb) (hx : c.slots = 0) (hn : 8 * c.exts + 7 ≤ N) (hN : N < 2 ^ 63) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := ⟨_, List.mem_append_right _ h.wr, by rw [he]; exact h.contains (by omega_using [hn, hk]) hN⟩
  baseAl _ := by rw [hb]; exact h.al
  extAl _ := by rw [he]; exact h.al
  slots := by omega_using [hx]
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
      exact Offset.disjoint_base b (by omega_using [hk]) (by omega_using [hk'])) (by decide)

theorem Ctx.masks {s₀ s : State} (hm : MasksAt s₀.mem (s₀.gpr sb) allKs) (hc : Ctx s₀ s) :
    MasksAt s.mem (s.gpr sb) allKs := by
  intro k v hk
  have := allKs_slots _ hk
  rw [hc.base, slot_kept hc.frame this.1 (by omega_using [this])]
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
    exact hs.contains (by omega_using [hn, hk']) (by decide)
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
  omega_using [hcs, ha]

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

end

end

/-!
# Bitslicing the round keys, on RISC-V

As on PPC64LE (`Proof/Aes/PPC64LE/Keys.lean`): the key loop of
`vg_aes_ctr32` and of the block functions bitslices each round key (loaded
as four identical blocks, a byte at a time, `Bytes.loadLE64_ok`) with
`toBs` and stores it in the scratch buffer, from the last round key down.
The stores are checked by evaluation over the naming domain
(`Bitslice.names`), `toBs` by its proof (`Layers.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Wp VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## Loading a round key -/

theorem keyLoad_ok {s : State} {sc : Addr} {off : Nat}
    (hr : ∃ k, 240 ≤ k ∧ (⟨sc, k⟩ : Region) ∈ s.rd ++ s.wr)
    (hb : s.gpr .a0 = sc + BitVec.ofNat 64 off) (hoff : off + 16 ≤ 240) :
    WP isa (.block keyLoad) s fun s' =>
      (∀ b < 4, s'.gpr (q b) = s.mem.readW (wordAddr (s.gpr .a0) 0) 64 ∧
        s'.gpr (q (b + 4)) = s.mem.readW (wordAddr (s.gpr .a0) 1) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) := by
  obtain hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      obtain ⟨k, hk, hr⟩ := hr
      refine ⟨_, hr, ?_⟩
      rw [hb, Offset.add_add]
      exact Offset.contains_base sc (by omega_using [hoff, hd, hk]) (by omega_using [hoff, hd])
  simp only [keyLoad]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hin 0 (by omega_using [])) (hin 4 (by omega_using []))) fun s₁ ⟨h0, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  obtain a₁ : s₁.gpr .a0 = s.gpr .a0 := g₁ _ (by decide) (by decide) (by decide)
  refine WP.mono (Bytes.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [a₁, rd₁, wr₁]; exact hin 8 (by omega_using []))
    (by rw [a₁, rd₁, wr₁]; exact hin 12 (by omega_using []))) fun s₂ ⟨h4, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  obtain q0 : s₂.gpr (q 0) = s.mem.readW (wordAddr (s.gpr .a0) 0) 64 := by
    rw [g₂ _ (by decide) (by decide) (by decide), h0]
  obtain q4 : s₂.gpr (q 4) = s.mem.readW (wordAddr (s.gpr .a0) 1) 64 := by
    rw [h4, a₁, m₁]
  simp only [movR]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain k0 : s₈.gpr (q 0) = s₂.gpr (q 0) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]
  obtain k4 : s₈.gpr (q 4) = s₂.gpr (q 4) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · have e4' : s₅.gpr (q 4) = s₂.gpr (q 4) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · exact ⟨k0.trans q0, k4.trans q4⟩
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, q0]
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e4', q4]
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), q0]
      · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), e4', q4]
    · refine ⟨?_, ?_⟩
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), q0]
      · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), e4', q4]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, m₁]
  · have hn : r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 ∧ r ≠ q 5 ∧ r ≠ q 6 ∧ r ≠ q 7 ∧ r ≠ q 0 ∧ r ≠ q 4 ∧
        r ≠ t0 ∧ r ≠ t1 := by
      revert hr; cases r <;> decide
    obtain ⟨n1, n2, n3, n5, n6, n7, n0, n4, nt0, nt1⟩ := hn
    rw [u₈.other _ n7, u₇.other _ n6, u₆.other _ n5, u₅.other _ n3, u₄.other _ n2, u₃.other _ n1,
      g₂ _ n4 nt0 nt1, g₁ _ n0 nt0 nt1]

/-! ## Storing it -/

def storeCfg : Cfg := { base := .a2, slots := 8, ext := .a2, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map .v, slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : check (names 64) storeCfg (fun _ => none) keyStore storeEnv storePost = true := by
  decide +kernel

theorem keyStore_noDst : keyStore.all (fun i => dst i == none) = true := by decide +kernel

theorem nameRel_fun {V : Nat → BitVec 64} (a : Nat) (x y : BitVec 64) (hx : NameRel V a x)
    (hy : NameRel V a y) : x = y := hx.trans hy.symm

theorem keyStore_ok {s : State} {X : Addr} (hs : Scr s X 2048) {off : Nat}
    (hb : s.gpr .a2 = s.gpr sb + BitVec.ofNat 64 off) (hoff : off + 64 ≤ 2040) (h8 : off % 8 = 0) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .a2) k) 64 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr .a2, 64⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyStore_check
  obtain hal : (s.gpr .a2).toNat % 8 = 0 := by rw [hb, hs.base]; exact align_al_add X h8
  obtain hok : Ok storeCfg s :=
    { slotIn := fun k hk => ⟨_, hs.wr, by
        show (⟨X, 2048⟩ : Region).Contains (wordAddr (s.gpr .a2) k) 8
        rw [wordAddr, hb, Offset.add_add]
        exact hs.contains (by simp only [storeCfg] at hk; omega_using [hoff, hk]) (by decide)⟩
      extIn := fun k hk => by simp [storeCfg] at hk
      baseAl := fun _ => hal
      extAl := fun _ => hal
      slots := by simp [storeCfg]
      sep := fun k _ j hj => by simp [storeCfg] at hj }
  let V : Nat → BitVec 64 := fun k => s.gpr (q k)
  obtain hrel : Rel (NameRel V) storeCfg (fun _ => none) storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [storeCfg] at hk)⟩
    simp only [storeEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain h1 := List.find?_some hk
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) nameRel_fun hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    obtain h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => dst i != some r) = true :=
        List.all_eq_true.mpr fun i hi => by
          rw [beq_iff_eq.mp (List.all_eq_true.mp keyStore_noDst i hi)]
          rfl
      simp [this])

/-! ## Stepping back -/

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .a0 = s.gpr .a0 - 16 ∧ s'.gpr .a2 = s.gpr .a2 - 64 ∧ s'.gpr .a1 = s.gpr .a1 - 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [keyStep, runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_cons, exec_addi (by decide), runStep_some,
    runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
  simp only [State.write]
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial, trivial⟩
  · simp only [ite_true, show ¬ (Reg.a0 = Reg.a1) by decide, show ¬ (Reg.a0 = Reg.a2) by decide,
      ite_false, BitVec.sub_eq_add_neg]
    rfl
  · simp only [ite_true, show ¬ (Reg.a2 = Reg.a1) by decide, ite_false, BitVec.sub_eq_add_neg]
    rfl
  · simp only [ite_true, BitVec.sub_eq_add_neg]
    rfl

/-! ## Readings and regions -/

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 8) (ht : t < 8) :
    (m.readW a 64).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 64 by omega_arith]

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `X`, rounded to `b`, with
the masks; the key schedule `w` at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (X b sc : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : Scr s₀ X 2048
  base : s₀.gpr sb = b
  masks : MasksAt s₀.mem b allKs
  sch : ∃ k, 240 ≤ k ∧ (⟨sc, k⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sep : Region.Disjoint ⟨sc, 240⟩ ⟨X, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : Addr) (R i : Nat) : Addr := b + BitVec.ofNat 64 (1920 - 64 * (R - i))

/-- The memory the key loop writes. -/
abbrev kRegions (b : Addr) : List Region := [⟨b, 320⟩, ⟨b + BitVec.ofNat 64 1024, 960⟩]

/-- The registers the key loop writes. -/
def keyWrites : List Reg := sboxWrites ++ [.a0, .a1, .a2]

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  a1 : s.gpr .a1 = BitVec.ofNat 64 (j + 1)
  a0 : s.gpr .a0 = sc + BitVec.ofNat 64 (16 * j)
  a2 : s.gpr .a2 = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : Addr) (R : Nat) (w : List Byte) (s : State) : Prop where
  a2 : s.gpr .a2 = keyAddr b R 0 - 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

theorem frame_regions {s₀ : State} {X b : Addr} (hs : Scr s₀ X 2048) (hb : s₀.gpr sb = b) :
    ∀ r ∈ kRegions b, Region.Sub r ⟨X, 2048⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := pad_lt X
  rcases hr with rfl | rfl
  · rw [← hb, hs.base]; exact Offset.sub_base X (by omega_using [this])
  · rw [← hb]; exact hs.sub (by omega_using [])

theorem wordAddr_off (b : Addr) (x k : Nat) : wordAddr (b + BitVec.ofNat 64 x) k = b + BitVec.ofNat 64 (x + 8 * k) := by
  rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_off_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m') {x : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 x, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 x) 64 = m.readW (b + BitVec.ofNat 64 x) 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) {i : Nat}
    (hi16 : i < 16) : s.mem (sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [roundKey_getD hi16, hk.w _ (by omega_arith)]
  refine hi.frame _ fun r hr hc => ?_
  obtain hsub := frame_regions hk.scr hk.base r hr
  refine hk.sep _ ?_ (hsub _ hc)
  simp only [Region.Contains]
  rw [show sc + BitVec.ofNat 64 (16 * j + i) - sc = BitVec.ofNat 64 (16 * j + i) from
      VG.Offset.add_sub_cancel_left _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The masks stay. -/
theorem masks_kept {m₀ m : Mem} {b : Addr} (hf : Frame (kRegions b) m₀ m) (hm : MasksAt m₀ b allKs) :
    MasksAt m b allKs := by
  intro k v hk
  have := allKs_slots _ hk
  rw [← hm k v hk]
  refine hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base b (by omega) (by omega)
  · exact Offset.disjoint b (by omega) (by omega) (by omega_using [])

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 64} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ keyWrites) :
    r ∉ sboxWrites ∧ r ≠ .a0 ∧ r ≠ .a2 ∧ r ≠ .a1 := by
  revert hr; cases r <;> decide

theorem add_ofNat_sub (b : Addr) {x y : Nat} (h : y ≤ x) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x - y) := by
  rw [show x = (x - y) + y by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_succ_sub_one (j : Nat) : BitVec.ofNat 64 (j + 1) - 1 = BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem keyAddr_pred (b : Addr) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    keyAddr b R j - 64 = keyAddr b R (j - 1) := by
  simp only [keyAddr]
  obtain T := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (show (List.range 15).all (fun R =>
      (List.range 15).all fun j => decide (j ≤ R → 0 < j →
        1920 - 64 * (R - j) = (1920 - 64 * (R - (j - 1))) + 64)) = true by decide +kernel) R
      (List.mem_range.mpr (by omega_using [hR]))) j (List.mem_range.mpr (by omega_using [hR, hjR])))
  rw [T hjR hj, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_ne_zero {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j != 0) = decide (j ≠ 0) := by
  by_cases h0 : j = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 j ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
      exact h0 this
    simpa [h0] using this

theorem eval_nonzero_ofNat {s : State} {r : Reg} {j : Nat} (hr : s.gpr r = BitVec.ofNat 64 j)
    (h : j < 2 ^ 64) : isa.eval (.nonzero r) s = some (decide (j ≠ 0)) := by
  simp only [RISCV64.eval, hr, ofNat_ne_zero h]

theorem keyBody_ok {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ isa.eval (.nonzero .a1) s' = some false ∧ KDone s₀ b R w s') ∨
      (0 < j ∧ isa.eval (.nonzero .a1) s' = some true ∧ KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  obtain hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  obtain hscr : Scr s X 2048 := hk.scr.congr hi.wr (by rw [hsb, hk.base])
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  refine WP.mono (keyLoad_ok (sc := sc) (off := 16 * j) (by rw [hi.rd, hi.wr]; exact hk.sch) hi.a0
    (by omega_arith)) fun s₁ ⟨hq₁, hrd₁, hwr₁, hsp₁, hm₁, hoth₁⟩ => ?_
  obtain hin : InRel (Q s₁) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    obtain hbyte := hi.sched hk hi16
    rw [getD_eq _ hi16, rkv, Vector.getElem_ofFn]
    simp only [Q]
    by_cases h8 : i < 8
    · rw [show bb + 4 * (i / 8) = bb by omega_arith, (hq₁ bb hb).1, show i % 8 = i by omega_arith,
        readW_bit _ _ h8 ht, wordAddr, hi.a0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
    · rw [show bb + 4 * (i / 8) = bb + 4 by omega_arith, (hq₁ bb hb).2, readW_bit _ _ (by omega_arith) ht,
        wordAddr, hi.a0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega_arith
  -- Bitslice it.
  obtain hsb₁ : s₁.gpr sb = b := by rw [hoth₁ sb (by decide), hsb]
  obtain hscr₁ : Scr s₁ X 2048 := hscr.congr hwr₁ (by rw [hsb₁, hsb])
  obtain hks₁ : MasksAt s₁.mem (s₁.gpr sb) bsKs := by
    rw [hm₁, hsb₁]
    exact masksAt_sub (masks_kept hi.frame hk.masks) fun p hp => by
      simp only [allKs, List.mem_append]; exact .inl (.inl hp)
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hfr₂⟩ :=
    toBs_ok (hscr₁.okExts rfl rfl rfl (by decide) (by decide)) hks₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  obtain hbs₂ := bs_of_in hq₂ hin
  obtain hm₂ : s₂.mem = s₁.mem := by
    funext x
    exact hfr₂ x fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, bsCfg, Region.Contains] at hc
  -- Store it.
  obtain hr5₂ : s₂.gpr .a2 = keyAddr b R j := by
    rw [hoth₂ .a2 (by decide), hoth₁ .a2 (by decide), hi.a2]
  obtain hscr₂ : Scr s₂ X 2048 := hscr₁.congr hwr₂ (hoth₂ sb (by decide))
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hsp₃, hg₃, hfr₃⟩ := keyStore_ok hscr₂
    (off := 1920 - 64 * (R - j)) (by rw [hr5₂, hoth₂ sb (by decide), hsb₁]) (by omega_arith)
    (by omega_arith)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hr3₄, hr5₄, hr4₄, hoth₄, hm₄, hrd₄, hwr₄, hsp₄⟩ := keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  -- What is kept.
  obtain hkeep : ∀ r, r ∉ keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  obtain hfr : Frame (kRegions b) s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁, ← hm₂]
    refine hfr₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hr5₂]
    exact Offset.sub b (by omega_arith) (by omega_arith)
  -- The keys stored before.
  obtain hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [hm₄, readW_off_frame hfr₃ fun r hr => ?_, hm₂, hm₁]
    simp only [List.mem_singleton] at hr; subst hr
    rw [hr5₂]
    exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  -- The key stored now.
  obtain hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R j) k) 64) (roundKey w j) :=
    keyRel_congr (keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hr5₂, hst₃ k hk]
  obtain hr4 : s₃.gpr .a1 = BitVec.ofNat 64 (j + 1) := by
    rw [hg₃, hoth₂ .a1 (by decide), hoth₁ .a1 (by decide), hi.a1]
  obtain hr3 : s₃.gpr .a0 = sc + BitVec.ofNat 64 (16 * j) := by
    rw [hg₃, hoth₂ .a0 (by decide), hoth₁ .a0 (by decide), hi.a0]
  obtain hr5 : s₃.gpr .a2 = keyAddr b R j := by rw [hg₃, hr5₂]
  obtain hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  obtain hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  obtain hsp : s₄.sp = s₀.sp := by rw [hsp₄, hsp₃, hsp₂, hsp₁, hi.sp]
  obtain hr4' : s₄.gpr .a1 = BitVec.ofNat 64 j := by rw [hr4₄, hr4, ofNat_succ_sub_one]
  obtain hev := eval_nonzero_ofNat hr4' (by omega_arith)
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hev, ⟨by rw [hr5₄, hr5], hrd, hwr, hsp, hkeep, hfr,
      fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega_arith) hiR
  · refine .inr ⟨by omega_arith, by simpa [h0] using hev, ⟨by omega_arith, ?_, ?_, ?_, hrd, hwr, hsp,
      hkeep, hfr, ?_⟩⟩
    · rw [hr4', show j - 1 + 1 = j by omega_arith]
    · rw [hr3₄, hr3, show 16 * (j - 1) = 16 * j - 16 by omega_arith]
      exact add_ofNat_sub sc (y := 16) (by omega_arith)
    · rw [hr5₄, hr5]; exact keyAddr_pred b hk.rounds (by omega_arith) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega_arith) hiR

theorem keyLoop_ok {s₀ : State} {X b sc : Addr} {R : Nat} {w : List Byte}
    (hk : KSetup s₀ X b sc R w) {s : State} (hi : KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) (.nonzero .a1)) s (KDone s₀ b R w) := by
  refine WP.loop (M := isa) (KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨hcf, hd⟩
  · exact .inr ⟨hcf, n - 1, by omega_arith, hi'⟩

end VG.Proof.Aes.RISCV64

end

end

/-!
# Facts the AES groups share, on RISC-V

Addresses and memory, the branch on the number of blocks left, and the
round keys and masks a group keeps, for the group loops of `vg_aes_ctr32`
(`Group.lean`) and of the block functions (`Ecb.lean`), as on x86-64
(`Proof/Aes/X86_64/Group.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## Doublewords of the data, a byte at a time or aligned -/

open VG.Impl.Words.RISCV64 (loadLE64W storeLE64W) in
/-- `loadLE64W w`: as `Bytes.loadLE64_ok`, the address a multiple of 8 when `w`. -/
theorem loadLE64W_ok {s : State} {w : Bool} {d tmp hi n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n)
    (hhn : hi ≠ n) (hdt : d ≠ tmp) (hdh : d ≠ hi) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (hal : w = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0) :
    WP isa (.block (loadLE64W w d tmp hi n off)) s fun s' =>
      s'.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      (∀ r, r ≠ d → r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases w with
  | false =>
    exact Bytes.loadLE64_ok hdn htn hhn hdt hdh hth ho (Words64.in_lo h8) (Words64.in_hi h8)
  | true =>
    exact wp_ld (by omega_using [ho]) rfl (hal rfl) h8 fun s' u =>
      WP.block_nil ⟨u.gpr, fun r h₁ _ _ => u.other r h₁, u.mem, u.rd, u.wr, u.sp⟩

open VG.Impl.Words.RISCV64 (loadLE64W storeLE64W) in
/-- `storeLE64W w`: as `Bytes.storeLE64_ok`, the address a multiple of 8 when `w`. -/
theorem storeLE64W_ok {s : State} {w : Bool} {v tmp hi n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (hhn : hi ≠ n) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h8 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8)
    (hal : w = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0) :
    WP isa (.block (storeLE64W w v tmp hi n off)) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32)).writeW
        (s.gpr n + BitVec.ofNat 64 (off + 4)) ((s.gpr v >>> 32).setWidth 32) ∧
      (∀ r, r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases w with
  | false =>
    exact Bytes.storeLE64_ok htv htn hhn hth ho (Words64.in_lo h8) (Words64.in_hi h8)
  | true =>
    exact wp_sd (by omega_using [ho]) rfl (hal rfl) h8 fun s' u =>
      WP.block_nil ⟨by rw [u.mem, ← Offset.add_add, Words64.writeW64_split], fun r _ _ => by rw [u.gpr],
        u.rd, u.wr, u.sp⟩

/-- `x &&& 7`, the address modulo 8. -/
theorem and7 (x : BitVec 64) : x &&& BitVec.ofInt 64 7 = BitVec.ofNat 64 (x.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega_using []

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega_arith)⟩

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem add_off8 (A : Addr) (x : Nat) :
    A + BitVec.ofNat 64 (x + 8) = A + BitVec.ofNat 64 x + 8 := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

theorem ofNat_sub_ofNat' {x y : Nat} (h : y ≤ x) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) := Offset.ofNat_sub_ofNat h

theorem off_add64 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 64 = D + BitVec.ofNat 64 (64 * (g + 1)) :=
  (Offset.add_add D _ 64).trans (by rw [show 64 * g + 64 = 64 * (g + 1) by omega_arith])

theorem ofNat_shr2 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 2 = BitVec.ofNat 64 (a / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [h])]

/-- The branch on `t0 := a4 >>> 2`: four blocks or more left. -/
theorem shr2_wp {s : State} {k : Nat} (hk : k < 2 ^ 64) (h7 : s.gpr .a4 = BitVec.ofNat 64 k)
    {c : Prog isa} {P : State → Prop}
    (h : ∀ s', Upd s s' t0 (BitVec.ofNat 64 (k / 4)) →
      isa.eval (.nonzero t0) s' = some (decide (4 ≤ k)) → WP isa c s' P) :
    WP isa (.seq (.block [shrI t0 .a4 2]) c) s P := by
  refine WP.seq (wp_srl (by decide) fun s' u => WP.block_nil ?_)
  rw [h7, ofNat_shr2 hk] at u
  refine h s' u ?_
  rw [Steps.eval_nonzero_ofNat s' t0 (by omega_using [hk]) u.gpr]
  congr 1; exact decide_eq_decide.mpr (by omega_using [])

/-! ## What a group keeps -/

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + 1024, 960⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 64 (1920 - 64 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 64 (1920 - 64 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains _ hR hj hk) hd (by decide)

/-- The masks' slots: 52–57 and 64–75. -/
theorem allKs_in : ∀ p ∈ allKs, (52 ≤ p.1 ∧ p.1 < 58) ∨ (64 ≤ p.1 ∧ p.1 < 76) := by decide

/-- Memory outside both areas of masks keeps them. -/
theorem masks_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r) (h : MasksAt m b allKs) :
    MasksAt m' b allKs := by
  intro k v hk
  rw [← h k v hk]
  refine hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
  rcases allKs_in _ hk with hk' | hk'
  · exact (hd r hr).1.sub_left (Offset.sub b (by omega) (by omega))
  · exact (hd r hr).2.sub_left (Offset.sub b (by omega) (by omega))

/-- The scratch buffer's parts, at the rounded base `b = X + pad X`. -/
theorem scr_part (X : Addr) {d n : Nat} (h : d + n + 7 ≤ 2048) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X) + BitVec.ofNat 64 d, n⟩ ⟨X, 2048⟩ := by
  rw [Offset.add_add]
  have := pad_lt X
  exact Offset.sub_base X (by omega_using [h, this])

theorem scr_base (X : Addr) {n : Nat} (h : n + 7 ≤ 2048) :
    Region.Sub ⟨X + BitVec.ofNat 64 (pad X), n⟩ ⟨X, 2048⟩ := by
  have := pad_lt X
  exact Offset.sub_base X (by omega_using [h, this])

end VG.Proof.Aes.RISCV64
