module

public import VerifiedGarbage.Proof.Aes.X86.Sse.Layers
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Aes.Memory
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES in SSE2 registers on x86 (32-bit): the round keys and eight blocks

`Good` is what every phase of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_ctr32_to` keeps: `edi` at the scratch
buffer, `esp`, the arguments and the key schedule in memory. `keys_ok`:
`keys` leaves the bitsliced round keys in the scratch buffer (`KeysAt`).
`encrypt8_ok`: then `encrypt8` encrypts the eight blocks in the slots,
having written only the slots; the round loop's invariant is the
specification's `foldl` over the rounds done. `decrypt8_ok`: so does
`decrypt8` decrypt them.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.X86.StraightX VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.Impl.Aes.X86 (sb at_ argOp movI addI subI addR subR dbl movR)
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_sub wp_subi wp_ldm wp_stm wp_cmpi wp_test
  toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-- Where the code runs: the scratch buffer at `B`, the key schedule at `S`,
the arguments above `E`. -/
structure Env (rd wr : List Region) (B S E : BitVec 32) (R : Nat) : Prop where
  scr : reg32 B 2048 ∈ wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  sch : reg32 S 240 ∈ rd ++ wr
  fitS : S.toNat + 240 ≤ 2 ^ 32
  sepS : (reg32 S 240).Disjoint (reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : ∀ i < 2, InRegions (rd ++ wr) (addr E (4 + 4 * i)) 4
  argSep : ∀ i < 2, Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 B 2048)

/-- What every phase keeps. -/
structure Good (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  rd : s.rd = rd
  wr : s.wr = wr
  edi : s.gpr .edi = B
  esp : s.gpr .esp = E
  arg0 : s.mem.readW (addr E 4) 32 = S
  arg1 : s.mem.readW (addr E 8) 32 = BitVec.ofNat 32 R
  w : ∀ i < 16 * (R + 1), s.mem (addr S i) = w.getD i 0

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

theorem Env.hR (he : Env rd wr B S E R) : 2 ≤ R ∧ R ≤ 14 := by rcases he.rounds with h | h | h <;> omega_using [h]

/-- A step that writes, of memory, only parts of the scratch buffer. -/
theorem Good.step (he : Env rd wr B S E R) {s s' : State} (hg : Good rd wr B S E R w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hdi : s'.gpr .edi = s.gpr .edi) (hsp : s'.gpr .esp = s.gpr .esp) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, Region.Sub r (reg32 B 2048)) : Good rd wr B S E R w s' where
  rd := hrd.trans hg.rd
  wr := hwr.trans hg.wr
  edi := hdi.trans hg.edi
  esp := hsp.trans hg.esp
  arg0 := by
    rw [← hg.arg0]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (he.argSep 0 (by decide)).sub_right (hs r hr)) (by decide)
  arg1 := by
    rw [← hg.arg1]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (he.argSep 1 (by decide)).sub_right (hs r hr)) (by decide)
  w := fun i hi => by
    rw [← hg.w i hi]
    have := he.hR
    exact hf _ fun r hr hc => he.sepS _ (reg_contains he.fitS (by omega_using [hi, this]) (by decide)) (hs r hr _ hc)

/-- A step that writes no memory, and neither `edi` nor `esp`. -/
theorem Good.upd (he : Env rd wr B S E R) {s s' : State} {d : Reg} {v : BitVec 32} (hg : Good rd wr B S E R w s)
    (u : Upd s s' d v) (h1 : d ≠ .edi) (h2 : d ≠ .esp) : Good rd wr B S E R w s' :=
  hg.step he (rs := []) u.rd u.wr (u.other _ (Ne.symm h1)) (u.other _ (Ne.symm h2))
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

/-- The round key `j` at `ecx`. -/
theorem Good.rk (he : Env rd wr B S E R) {s : State} (hg : Good rd wr B S E R w s) {j : Nat} (hj : j ≤ R)
    (hc : s.gpr .ecx = S + BitVec.ofNat 32 (16 * j)) :
    RkRel (s.mem.readW (xAddr (s.gpr .ecx) 0) 128) (roundKey w j) := by
  intro i hi t ht
  have := he.hR
  have hS := he.fitS
  have e : (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
    simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true, List.getElem?_drop]
  rw [e, ← hg.w _ (by omega_using [hj, hi]), hc, xAddr, addr_add, Nat.mul_zero, Nat.add_zero,
    show addr S (16 * j + i) = addr S (16 * j) + BitVec.ofNat 64 i from
      (addr_add64 (by omega_using [hS, hj, hi, this])).symm,
    ← Mem.extractLsb'_read s.mem (addr S (16 * j)) (n := 16) hi, BitVec.getLsbD_extractLsb',
    decide_eq_true ht, Bool.true_and]
  rfl

/-! ## The bitsliced round keys -/

/-- The bitsliced round keys `1 … n`, in the scratch buffer. -/
def KeysAt (m : Mem) (B : BitVec 32) (w : List Byte) (n : Nat) : Prop :=
  ∀ j < n, KeyRel (fun k => m.readW (addr B (keysOff + 128 * j + 16 * k)) 128) (roundKey w (j + 1))

theorem keyRel_congr {K K' : Nat → BitVec 128} {rk : List Byte} (h : KeyRel K rk) (hk : ∀ k < 8, K' k = K k) :
    KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, hk j hj]

/-- A write apart from the round keys. -/
theorem KeysAt.frame {m m' : Mem} {n : Nat} (hn : n ≤ 13) (hfit : B.toNat + 2048 ≤ 2 ^ 32) (h : KeysAt m B w n)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr B keysOff, 1664⟩ r) :
    KeysAt m' B w n := fun j hj => keyRel_congr (h j hj) fun k hk =>
  hf.readW (r := ⟨addr B (keysOff + 128 * j + 16 * k), 16⟩) (Region.contains_self _ _) (fun r hr =>
    (hd r hr).sub_left (part_sub hfit (by decide) (by omega_using []) (by unfold keysOff; omega_using [hn, hj, hk])))
    (by decide)

theorem split_run {a b : List Instr} {s : State} {P : State → Prop}
    (h : ∃ s', runBlock isa a s = some s' ∧ WP isa (.block b) s' P) : WP isa (.block (a ++ b)) s P := by
  obtain ⟨s', hs', h'⟩ := h
  rw [WP.block_append_iff]
  exact WP.of_runBlock ⟨s', hs', h'⟩

/-- Before bitslicing round key `j + 1`. -/
structure KInv (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (m₀ : Mem) (j : Nat) (s : State) :
    Prop where
  hj : j < R - 1
  good : Good rd wr B S E R w s
  ecx : s.gpr .ecx = S + BitVec.ofNat 32 (16 * (j + 1))
  esi : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * j)
  edx : s.gpr .edx = BitVec.ofNat 32 (R - 1 - j)
  frame : Frame [⟨addr B keysOff, 1664⟩] m₀ s.mem
  keys : KeysAt s.mem B w j

theorem keyBody_ok (he : Env rd wr B S E R) {m₀ : Mem} {j : Nat} {s : State} (hi : KInv rd wr B S E R w m₀ j s) :
    WP isa (.block keyBody) s fun s' =>
      (s'.zf = some true ∧ Good rd wr B S E R w s' ∧ Frame [⟨addr B keysOff, 1664⟩] m₀ s'.mem ∧
        KeysAt s'.mem B w (R - 1)) ∨
      (s'.zf = some false ∧ KInv rd wr B S E R w m₀ (j + 1) s') := by
  have hR := he.hR
  have hjR := hi.hj
  have fB := he.fitB
  have fS := he.fitS
  have hg := hi.good
  have hok : Ok bsKeyCfg s :=
    Ok.of_off (r := reg32 B 2048) (r' := reg32 S 240) (b := B) (b' := S) (off := keysOff + 128 * j)
      (off' := 16 * (j + 1)) (n := 2048) (n' := 240) (by rw [hg.wr]; exact he.scr) rfl fB (Nat.le_refl _)
      hi.esi (by simp only [bsKeyCfg, keysOff]; omega_using [hjR, hR]) (by simp only [keysOff]; omega_using [hjR, hR])
      (by rw [hg.rd, hg.wr]; exact he.sch) rfl fS (Nat.le_refl _) hi.ecx
      (by simp only [bsKeyCfg]; omega_using [hjR, hR]) (.inr (.inl he.sepS.symm))
  obtain ⟨s₁, hs₁, hout, hrd, hwr, hgp, hfr⟩ := linear_ok bsKey_check hok
    (fun _ => s.mem.readW (xAddr (s.gpr .ecx) 0) 128) (fun j i h _ => by cases h)
    (fun j hj => by
      have : j = 0 := by simp only [bsKeyCfg] at hj; omega_using [hj]
      subst this; exact ⟨by decide, rfl⟩)
  have hkey : KeyRel (fun k => s₁.mem.readW (xAddr (s.gpr kp) k) 128) (roundKey w (j + 1)) :=
    bs_key (fun j hj p hp => hout j _ _ (mem_qOuts hj) p hp) (hg.rk he (by omega_using [hjR]) hi.ecx)
  have g₁ : ∀ r, r ≠ .eax → s₁.gpr r = s.gpr r := fun r hr => hgp r (keep_eax bsKey_keeps hr)
  have hreg : slotRegion bsKeyCfg s = ⟨addr B (keysOff + 128 * j), 128⟩ := by
    simp only [slotRegion, bsKeyCfg]; rw [show s.gpr kp = _ from hi.esi]; rfl
  rw [hreg] at hfr
  have hsub : Region.Sub ⟨addr B (keysOff + 128 * j), 128⟩ ⟨addr B keysOff, 1664⟩ :=
    part_sub fB (by decide) (by omega_using []) (by unfold keysOff; omega_using [hjR, hR])
  have hg₁ : Good rd wr B S E R w s₁ := hg.step he hrd hwr (g₁ _ (by decide)) (g₁ _ (by decide)) hfr
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_sub_reg fB (by unfold keysOff; omega_using [hjR, hR]))
  have hf₁ : Frame [⟨addr B keysOff, 1664⟩] m₀ s₁.mem := hi.frame.trans (hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩)
  have hk₁ : KeysAt s₁.mem B w (j + 1) := fun i hij => by
    by_cases h : i = j
    · subst h
      refine keyRel_congr hkey fun k _ => ?_
      rw [show s.gpr kp = _ from hi.esi, xAddr, addr_add]
    · refine keyRel_congr (hi.keys i (by omega_using [hij, h])) fun k hk => ?_
      refine hfr.readW (r := ⟨addr B (keysOff + 128 * i + 16 * k), 16⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj fB (by unfold keysOff; omega_using [hij, hjR, hR, hk])
        (by unfold keysOff; omega_using [hjR, hR]) (.inl (by omega_using [hij, h, hk]))
  refine split_run ⟨s₁, hs₁, ?_⟩
  refine wp_addi fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ _ hz => WP.block_nil ?_
  have hg₄ : Good rd wr B S E R w s₄ := ((hg₁.upd he u₂ (by decide) (by decide)).upd he u₃ (by decide) (by decide)).upd he
    u₄ (by decide) (by decide)
  have hm₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have hdx : s₃.gpr .edx = BitVec.ofNat 32 (R - 1 - j) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hi.edx]
  rw [hdx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_ofNat (by omega_using [hjR]),
    ofNat_beq_zero (by omega_using [hR])] at hz
  by_cases hlast : j + 1 = R - 1
  · refine .inl ⟨by rw [hz, decide_eq_true (by omega_using [hlast])], hg₄, by rw [hm₄]; exact hf₁, ?_⟩
    rw [hm₄, ← hlast]; exact hk₁
  · refine .inr ⟨by rw [hz, decide_eq_false (by omega_using [hlast, hjR])],
      ⟨by omega_using [hlast, hjR], hg₄, ?_, ?_, ?_, by rw [hm₄]; exact hf₁, by rw [hm₄]; exact hk₁⟩⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide), hi.ecx, BitVec.add_assoc,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
      rfl
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁ _ (by decide), hi.esi, BitVec.add_assoc,
        show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, ← BitVec.ofNat_add]
      rfl
    · rw [u₄.gpr, hdx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_ofNat (by omega_using [hjR])]
      rfl

theorem keys_ok (he : Env rd wr B S E R) {s : State} (hg : Good rd wr B S E R w s) :
    WP isa keys s fun s' => Good rd wr B S E R w s' ∧ Frame [⟨addr B keysOff, 1664⟩] s.mem s'.mem ∧
      KeysAt s'.mem B w (R - 1) := by
  have hR := he.hR
  refine WP.seq ?_
  have argIn : ∀ (t : State), t.rd = rd → t.wr = wr → ∀ i < 2, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t h1 h2 i hi => by rw [h1, h2]; exact he.argIn i hi
  refine wp_ldm (B := E) (o := 4) hg.esp (argIn _ hg.rd hg.wr 0 (by decide)) fun s₁ u₁ => ?_
  have g₁ := hg.upd he u₁ (by decide) (by decide)
  refine wp_addi fun s₂ u₂ => ?_
  have g₂ := g₁.upd he u₂ (by decide) (by decide)
  refine wp_ldm (B := E) (o := 8) g₂.esp (argIn _ g₂.rd g₂.wr 1 (by decide)) fun s₃ u₃ => ?_
  have g₃ := g₂.upd he u₃ (by decide) (by decide)
  refine wp_subi fun s₄ u₄ _ _ => ?_
  have g₄ := g₃.upd he u₄ (by decide) (by decide)
  refine wp_mov fun s₅ u₅ => ?_
  have g₅ := g₄.upd he u₅ (by decide) (by decide)
  refine wp_addi fun s₆ u₆ => WP.block_nil ?_
  have g₆ := g₅.upd he u₆ (by decide) (by decide)
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hi : KInv rd wr B S E R w s.mem 0 s₆ := by
    refine ⟨by omega_using [hR], g₆, ?_, ?_, ?_, by rw [hm]; exact Frame.refl _ _, fun j hj => absurd hj (by omega_using [])⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.gpr, hg.arg0]; rfl
    · rw [u₆.gpr, u₅.gpr, show s₄.gpr sb = B from g₄.edi]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.mem, u₁.mem, hg.arg1,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_ofNat (by omega_using [hR])]; rfl
  refine WP.loop (M := isa) (fun n s' => ∃ j, n = R - 1 - j ∧ KInv rd wr B S E R w s.mem j s')
    (fun n s' ⟨j, hn, hi⟩ => WP.mono (keyBody_ok he hi) fun t h => ?_) (R - 1) s₆ ⟨0, rfl, hi⟩
  rcases h with ⟨hz, h⟩ | ⟨hz, h⟩
  · exact .inl ⟨by simp [X86.eval, hz], h⟩
  · exact .inr ⟨by simp [X86.eval, hz], R - 1 - (j + 1), by have := hi.hj; omega_using [hn, this], j + 1, rfl, h⟩

/-! ## Eight blocks -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    midRounds w (m + 1) x = rnd w (m + 1) (midRounds w m x) := by
  simp [midRounds, List.range_succ, List.foldl_append]

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- What the rounds keep: `Good`, memory but for the slots, as it was in
`s₀`, and the registers but `eax`, `ecx` and `esi`. -/
structure RGood (rd wr : List Region) (B S E : BitVec 32) (R : Nat) (w : List Byte) (s₀ s : State) :
    Prop where
  good : Good rd wr B S E R w s
  frame : Frame [reg32 B 272] s₀.mem s.mem
  keys : KeysAt s.mem B w (R - 1)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → s.gpr r = s₀.gpr r

theorem slots_sub : ∀ r ∈ [reg32 B 272], Region.Sub r (reg32 B 2048) := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])

theorem keys_slots (hfit : B.toNat + 2048 ≤ 2 ^ 32) :
    ∀ r ∈ [reg32 B 272], Region.Disjoint ⟨addr B keysOff, 1664⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨B.setWidth 64, 272⟩
  rw [← addr_zero]
  exact part_disj hfit (by decide) (by decide) (.inr (by decide))

theorem RGood.step (he : Env rd wr B S E R) {s₀ : State} {s s' : State} (hg : RGood rd wr B S E R w s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → s'.gpr r = s.gpr r)
    (hf : Frame [reg32 B 272] s.mem s'.mem) : RGood rd wr B S E R w s₀ s' where
  good := hg.good.step he hrd hwr (hk _ (by decide) (by decide) (by decide))
    (hk _ (by decide) (by decide) (by decide)) hf slots_sub
  frame := hg.frame.trans hf
  keys := hg.keys.frame (by have := he.hR; omega_using [this]) he.fitB hf (keys_slots he.fitB)
  keep := fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hg.keep r h1 h2 h3)

theorem RGood.upd (he : Env rd wr B S E R) {s₀ : State} {s s' : State} {d : Reg} {v : BitVec 32}
    (hg : RGood rd wr B S E R w s₀ s) (u : Upd s s' d v) (hd : d = .eax ∨ d = .ecx ∨ d = .esi) :
    RGood rd wr B S E R w s₀ s' :=
  hg.step he u.rd u.wr (fun r h1 h2 h3 => u.other r (by rintro rfl; simp [h1, h2, h3] at hd))
    (by rw [u.mem]; exact Frame.refl _ _)

theorem Q_congr {s s' : State} (hb : s'.gpr .edi = s.gpr .edi) (hm : s'.mem = s.mem) : Q s' = Q s := by
  funext i; simp only [Q]; rw [show s'.gpr sb = s.gpr sb from hb, hm]

theorem RGood.slotsR {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) : slotsR s = reg32 B 272 := by
  simp only [Sse.slotsR]; rw [show s.gpr sb = B from hg.good.edi]; rfl

theorem RGood.sboxOk (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) :
    Ok sboxCfg s :=
  Ok.of_off (r := reg32 B 2048) (r' := reg32 B 2048) (b := B) (b' := B) (off := 0) (off' := 0) (n := 2048)
    (n' := 2048) (by rw [hg.good.wr]; exact he.scr) rfl he.fitB (Nat.le_refl _)
    (by show s.gpr .edi = _; rw [hg.good.edi]; simp) (by decide) (by decide)
    (by rw [hg.good.rd, hg.good.wr]; exact List.mem_append_right _ he.scr) rfl he.fitB (Nat.le_refl _)
    (by show s.gpr .edi = _; rw [hg.good.edi]; simp) (by decide) (.inl rfl)

theorem RGood.keyOk (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {j : Nat}
    (hj : j ≤ R) (hc : s.gpr .ecx = S + BitVec.ofNat 32 (16 * j)) : Ok keyCfg s :=
  Ok.of_off (r := reg32 B 2048) (r' := reg32 S 240) (b := B) (b' := S) (off := 0) (off' := 16 * j) (n := 2048)
    (n' := 240) (by rw [hg.good.wr]; exact he.scr) rfl he.fitB (Nat.le_refl _)
    (by show s.gpr .edi = _; rw [hg.good.edi]; simp) (by decide) (by decide)
    (by rw [hg.good.rd, hg.good.wr]; exact he.sch) rfl he.fitS (Nat.le_refl _) hc
    (by have := he.hR; simp only [keyCfg]; omega_using [this, hj]) (.inr (.inl he.sepS.symm))

theorem RGood.roundOk (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {j : Nat}
    (hj : j < R - 1) (hk : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * j)) : Ok roundCfg s :=
  Ok.of_off (r := reg32 B 2048) (r' := reg32 B 2048) (b := B) (b' := B) (off := 0) (off' := keysOff + 128 * j)
    (n := 2048) (n' := 2048) (by rw [hg.good.wr]; exact he.scr) rfl he.fitB (Nat.le_refl _)
    (by show s.gpr .edi = _; rw [hg.good.edi]; simp) (by decide) (by decide)
    (by rw [hg.good.rd, hg.good.wr]; exact List.mem_append_right _ he.scr) rfl he.fitB (Nat.le_refl _) hk
    (by have := he.hR; simp only [roundCfg, keysOff]; omega_using [this, hj])
    (.inr (.inr ⟨rfl, .inl (by simp only [roundCfg, slots, keysOff]; omega_using [])⟩))

/-- The S-box. -/
theorem sbox_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s)
    {T : Nat → Spec.Aes.State} (hbs : BsRel (Q s) T) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → (∀ r, s'.gpr r = s.gpr r) →
      BsRel (Q s') (fun b => x63 (subBytes (T b))) → WP isa (.block rest) s' P) :
    WP isa (.block (sboxCode ++ rest)) s P := by
  obtain ⟨s', hs', hq, hrd, hwr, hgp, hf⟩ := sbox_ok (hg.sboxOk he)
  rw [hg.slotsR] at hf
  exact split_run ⟨s', hs', h s' (hg.step he hrd hwr (fun r _ _ _ => hgp r) hf) hgp (bs_sub hq hbs)⟩

/-- The round key `j` of the schedule at `ecx`, and a layer that takes it. -/
theorem key_layer (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {j : Nat}
    (hj : j ≤ R) (hc : s.gpr .ecx = S + BitVec.ofNat 32 (16 * j)) {is : List Instr} {cst : Nat → Nat}
    {g : Nat → Nat → List Nat}
    (hchk : check (Bitslice.lanes 128 11) keyCfg is (linEnv slots 1 8 qIns) (linPost slots 11 (qOuts cst g)) = true)
    (hk : (is.all fun i => i.dst == none || i.dst == some .eax) = true) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      (∃ W : Nat → BitVec 128, (∀ j < 8, W j = Q s j) ∧ RkRel (W 8) (roundKey w j) ∧
        ∀ j < 8, ∀ p < 128, (Q s' j).getLsbD p = ((cst j).testBit p ^^ Bitslice.xorBits W (g j p))) →
      WP isa (.block rest) s' P) :
    WP isa (.block (is ++ rest)) s P := by
  let W : Nat → BitVec 128 := fun k => if k < 8 then Q s k else s.mem.readW (xAddr (s.gpr .ecx) 0) 128
  obtain ⟨s', hs', hq, hrd, hwr, hgp, hf⟩ := round_layer (c := keyCfg) rfl rfl hchk (hg.keyOk he hj hc) (by decide) W
    (fun k hk => by simp only [W, hk, ite_true])
    (fun k hk => by
      have : k = 0 := by simp only [keyCfg] at hk; omega_using [hk]
      subst this; rfl) (keep_eax hk (by decide))
  rw [hg.slotsR] at hf
  have hgp' : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => hgp r (keep_eax hk hr)
  refine split_run ⟨s', hs', h s' (hg.step he hrd hwr (fun r h1 _ _ => hgp' r h1) hf) hgp'
    ⟨W, fun k hk => by simp only [W, hk, ite_true], ?_, hq⟩⟩
  have := hg.good.rk he hj hc
  exact this

theorem RGood.argIn (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {i : Nat}
    (hi : i < 2) : InRegions (s.rd ++ s.wr) (addr E (4 + 4 * i)) 4 := by
  rw [hg.good.rd, hg.good.wr]; exact he.argIn i hi

/-- The words the rest of a round takes: the state's, and the round key's at `kp`. -/
def roundW (s : State) (k : Nat) : BitVec 128 :=
  if k < 8 then Q s k else s.mem.readW (xAddr (s.gpr kp) (k - 8)) 128

theorem roundW_lt {s : State} {k : Nat} (hk : k < 8) : roundW s k = Q s k := by rw [roundW, ite_eq_left hk]

theorem roundW_key {s : State} (k : Nat) : roundW s (8 + k) = s.mem.readW (xAddr (s.gpr kp) k) 128 := by
  rw [roundW, ite_eq_right (by omega_using []), Nat.add_sub_cancel_left]

theorem bsRel_congr {Q Q' : Nat → BitVec 128} {T : Nat → Spec.Aes.State} (h : BsRel Q T)
    (hq : ∀ j < 8, Q' j = Q j) : BsRel Q' T := fun b hb i hi => by
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, hq j hj]

/-- The rest of a round, from the S-box. -/
theorem linear_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {m : Nat}
    (hm : m < R - 1) (hk : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * m)) {T : Nat → Spec.Aes.State}
    (hbs : BsRel (Q s) (fun b => x63 (subBytes (T b)))) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → (∀ r, s'.gpr r = s.gpr r) →
      BsRel (Q s') (fun b => rnd w (m + 1) (T b)) → WP isa (.block rest) s' P) :
    WP isa (.block (linear ++ rest)) s P := by
  obtain ⟨s', hs', hq, hrd, hwr, hgp, hf⟩ := round_layer (c := roundCfg) rfl rfl linear_check
    (hg.roundOk he hm hk) (by decide) (roundW s) (fun k hk => roundW_lt hk) (fun k _ => roundW_key k)
    (keep_all linear_keeps _)
  rw [hg.slotsR] at hf
  have hgp' : ∀ r, s'.gpr r = s.gpr r := fun r => hgp r (keep_all linear_keeps r)
  refine split_run ⟨s', hs', h s' (hg.step he hrd hwr (fun r _ _ _ => hgp' r) hf) hgp'
    (bs_linear (W := roundW s) (T := fun b => subBytes (T b)) (fun j hj p hp => ?_)
      (bsRel_congr hbs fun j hj => roundW_lt hj) (keyRel_congr (hg.keys m hm) fun k _ => ?_))⟩
  · rw [hq j hj p hp, Nat.zero_testBit, Bool.false_xor]
  · rw [roundW_key, hk, xAddr, addr_add]

/-- A middle round. -/
theorem round_ok (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {m : Nat}
    (hm : m < R - 1) (hk : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * m))
    (hn : s.gpr .eax = BitVec.ofNat 32 (R - 1 - m)) (hc : s.gpr .ecx = S) {T : Nat → Spec.Aes.State}
    (hbs : BsRel (Q s) T) :
    WP isa (.block roundBody) s fun s' => RGood rd wr B S E R w s₀ s' ∧
      s'.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (m + 1)) ∧ s'.gpr .eax = BitVec.ofNat 32 (R - 1 - (m + 1)) ∧
      s'.gpr .ecx = S ∧ BsRel (Q s') (fun b => rnd w (m + 1) (T b)) ∧ s'.zf = some (decide (m + 1 = R - 1)) := by
  have hR := he.hR
  simp only [roundBody, List.append_assoc]
  refine sbox_wp he hg hbs fun s₁ h₁ g₁ hbs₁ => linear_wp he h₁ hm (by rw [g₁, hk]) hbs₁ fun s₂ h₂ g₂ hbs₂ =>
    wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ _ hz => WP.block_nil ?_
  have hax : s₃.gpr .eax = BitVec.ofNat 32 (R - 1 - m) := by rw [u₃.other _ (by decide), g₂, g₁, hn]
  have hsub : BitVec.ofNat 32 (R - 1 - m) - 1 = BitVec.ofNat 32 (R - 1 - (m + 1)) :=
    Wp.sub_ofNat (b := 1) (by omega_using [hm])
  refine ⟨(h₂.upd he u₃ (by decide)).upd he u₄ (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, g₂, g₁, hk, BitVec.add_assoc,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, ← BitVec.ofNat_add, Nat.add_assoc, ← Nat.mul_succ]
  · rw [u₄.gpr, hax, hsub]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, g₁, hc]
  · rw [Q_congr (s := s₂) (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.mem, u₃.mem])]
    exact hbs₂
  · rw [hz, hax, hsub, ofNat_beq_zero (by omega_using [hR])]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hm], fun h => by omega_using [h]⟩)

/-- `ecx :=` the last round key of the schedule, from `ecx` at the first. -/
theorem lastKeyPtr_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s)
    (hc : s.gpr .ecx = S) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → s'.gpr .ecx = S + BitVec.ofNat 32 (16 * R) → Q s' = Q s →
      WP isa (.block rest) s' P) : WP isa (.block (lastKeyPtr ++ rest)) s P := by
  have hR := he.hR
  simp only [lastKeyPtr, List.append_assoc]
  refine wp_ldm (B := E) (o := 8) hg.good.esp (hg.argIn he (i := 1) (by decide)) fun s₂ u₂ => ?_
  have h₂ := hg.upd he u₂ (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => wp_add fun s₆ u₆ _ =>
    wp_add fun s₇ u₇ _ => ?_
  have h₇ := ((((h₂.upd he u₃ (by decide)).upd he u₄ (by decide)).upd he u₅ (by decide)).upd he u₆ (by decide)).upd he u₇ (by decide)
  refine h s₇ h₇ ?_ (Q_congr (by rw [h₇.good.edi, hg.good.edi]) (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]))
  rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₆.other .ecx (by decide), u₅.other .ecx (by decide),
    u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide), hc, hg.good.arg1]
  congr 1
  bv_omega_using [hR]

/-- Eight blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt8_ok (he : Env rd wr B S E R) {s₀ : State} (hg₀ : Good rd wr B S E R w s₀)
    (hk₀ : KeysAt s₀.mem B w (R - 1)) {T : Nat → Spec.Aes.State} (hin : InRel (Q s₀) T) :
    WP isa encrypt8 s₀ fun s => RGood rd wr B S E R w s₀ s ∧ InRel (Q s) (fun b => cipher R w (T b)) := by
  have hR := he.hR
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (T b) (roundKey w 0)
  have hg : RGood rd wr B S E R w s₀ s₀ := ⟨hg₀, Frame.refl _ _, hk₀, fun _ _ _ _ => rfl⟩
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m < R - 1 ∧ RGood rd wr B S E R w s₀ s ∧
    s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * m) ∧ s.gpr .eax = BitVec.ofNat 32 (R - 1 - m) ∧
    s.gpr .ecx = S ∧ BsRel (Q s) (fun b => midRounds w m (A b))
  let Mid : State → Prop := fun s => RGood rd wr B S E R w s₀ s ∧ s.gpr .ecx = S ∧
    BsRel (Q s) (fun b => midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- The first round key, and bitsliced.
    simp only [List.append_assoc]
    refine wp_ldm (B := E) (o := 4) hg.good.esp (hg.argIn he (i := 0) (by decide)) fun s₁ u₁ => ?_
    have h₁ := hg.upd he u₁ (by decide)
    have hq₁ : Q s₁ = Q s₀ := Q_congr (u₁.other _ (by decide)) u₁.mem
    have hc₁ : s₁.gpr .ecx = S := by rw [u₁.gpr]; exact hg₀.arg0
    refine key_layer he h₁ (j := 0) (by omega_using [hR]) (by rw [hc₁]; simp) toBs_check toBs_keeps
      fun s₂ h₂ g₂ ⟨W, hW, hrk, hq₂⟩ => ?_
    have hbs₂ : BsRel (Q s₂) A := bs_toBs (W := W) (fun j hj p hp => by rw [hq₂ j hj p hp]; simp)
      (fun b hb i hi j hj => by rw [hW b hb, hq₁]; exact hin b hb i hi j hj) hrk
    refine wp_mov fun s₃ u₃ => ?_
    have h₃ := h₂.upd he u₃ (by decide)
    refine wp_addi fun s₄ u₄ => ?_
    have h₄ := h₃.upd he u₄ (by decide)
    refine wp_ldm (B := E) (o := 8) h₄.good.esp (h₄.argIn he (i := 1) (by decide)) fun s₅ u₅ => ?_
    have h₅ := h₄.upd he u₅ (by decide)
    refine wp_subi fun s₆ u₆ _ _ => WP.block_nil ?_
    have h₆ := h₅.upd he u₆ (by decide)
    refine ⟨0, rfl, by omega_using [hR], h₆, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, show s₂.gpr sb = B from h₂.good.edi]; rfl
    · rw [u₆.gpr, u₅.gpr, h₄.good.arg1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        Wp.sub_ofNat (by omega_using [hR])]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        g₂ _ (by decide), hc₁]
    · rw [Q_congr (s := s₂) (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide)]) (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem])]
      exact hbs₂
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hg, hk, hn, hc, hbs⟩ := hs
    refine WP.mono (round_ok he hg hm hk hn hc hbs) fun s' ⟨hg', hk', hn', hc', hbs', hz⟩ => ?_
    by_cases hlast : m + 1 = R - 1
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hg', hc', ?_⟩
      rw [← hlast]
      intro b hb i hi
      rw [hbs' b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega_using [hm], m + 1, rfl,
        by omega_using [hm, hlast], hg', hk', hn', hc', fun b hb i hi => by
          rw [hbs' b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hg, hc, hbs⟩ := h
    simp only [List.append_assoc]
    refine sbox_wp he hg hbs fun s₁ h₁ g₁ hbs₁ => ?_
    refine lastKeyPtr_wp he h₁ (by rw [g₁, hc]) fun s₇ h₇ hc₇ hq₇ => ?_
    rw [← List.append_nil fromBs]
    refine key_layer he h₇ (j := R) (Nat.le_refl _) hc₇ fromBs_check fromBs_keeps
      fun s₈ h₈ _ ⟨W, hW, hrk, hq₈⟩ => WP.block_nil ⟨h₈, ?_⟩
    have := bs_fromBs (W := W) (T := fun b => subBytes (midRounds w (R - 1) (A b))) hq₈ (fun b hb i hi => by
      rw [← hbs₁ b hb i hi]
      exact byte_ext fun j hj => by
        rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, hW j hj, hq₇]) hrk
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; rfl

end

/-! ## The inverse cipher -/

open VG.Bitslice
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns invSbox)
open VG.Proof.Aes.Vector (getD_addRoundKey getD_invMixColumns getD_invShiftRows getD_invSubBytes st_ext)

theorem xorBits_append {w : Nat} (W : Nat → BitVec w) (l₁ l₂ : List Nat) :
    xorBits W (l₁ ++ l₂) = (xorBits W l₁ ^^ xorBits W l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l ih => rw [List.cons_append, xorBits_cons, xorBits_cons, ih, Bool.xor_assoc]

theorem invSrc_pos : ∀ b < 8, ∀ i < 16, invSrc (pos b i) = pos b (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by decide
theorem down_pos : ∀ b < 8, ∀ i < 16, ∀ k < 4, down (pos b i) k = pos b ((i % 4 + k) % 4 + 4 * (i / 4)) := by decide

theorem bs_invSub {Q Q' : Nat → BitVec 128} {T : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (invSbox (bsByte Q p ^^^ 0x63)).getLsbD j)
    (hr : BsRel Q fun b => x63 (T b)) : BsRel Q' fun b => invSubBytes (T b) := by
  intro b hb i hi
  rw [getD_invSubBytes _ hi]
  refine byte_ext fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), hr b hb i hi, getD_x63 _ hi, BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero]

theorem bs_invToBs {W Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = ((n63 j).testBit p ^^ xorBits W (toBsG j p)))
    (hr : InRel W S) (hk : RkRel (W 8) rk) : BsRel Q' fun b => x63 (addRoundKey (S b) rk) := by
  intro b hb i hi
  obtain ⟨h1, h2⟩ := pos_facts b hb i hi
  rw [getD_x63 _ hi, getD_addRoundKey _ _ hi]
  refine byte_ext fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), n63_bit (pos_lt hb hi), toBsG, h1, h2, xorBits_cons, xorBits_cons,
    xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega_using [hi, hj]), bitOf_word _ _ _ (by omega_using [hi, hj]),
    hr b hb i hi j hj, hk i hi j hj, BitVec.getLsbD_xor, BitVec.getLsbD_xor, Bool.xor_comm]
  rfl

theorem bs_invFromBs {W Q' : Nat → BitVec 128} {T : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ b < 8, ∀ t < 128, (Q' b).getLsbD t = xorBits W (invFromBsG b t)) (hr : BsRel W T) (hk : RkRel (W 8) rk) :
    InRel Q' fun b => addRoundKey (invShiftRows (T b)) rk := by
  intro b hb i hi j hj
  have hs : i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4) < 16 := by omega_using []
  have hlt : invSrc (pos b i) < 128 := by rw [invSrc_pos b hb i hi]; exact pos_lt hb hs
  rw [h b hb _ (by omega_using [hi, hj]), getD_addRoundKey _ _ hi, getD_invShiftRows _ hi,
    invFromBsG, show (8 * i + j) % 8 = j by omega_using [hj], show (8 * i + j) / 8 = i by omega_using [hj],
    xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hlt, bitOf_word _ _ _ (by omega_using [hi, hj]),
    ← getLsbD_bsByte _ _ hj, invSrc_pos b hb i hi, hr b hb _ hs, hk i hi j hj, BitVec.getLsbD_xor]

theorem xorBits_row {W : Nat → BitVec 128} {o q : Nat} (hq : q < 128) {ts : List Nat} (hts : ∀ t ∈ ts, t < 8) :
    xorBits W (ts.map fun t => 128 * (o + t) + q) = bitsXor (bsByte (fun t => W (o + t)) q) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, xorBits_cons, bitOf_word _ _ _ hq, ih fun u hu => hts u (List.mem_cons_of_mem _ hu)]
    simp only [bitsXor, List.foldr_cons]
    rw [getLsbD_bsByte _ _ (hts t List.mem_cons_self)]

theorem invLinearG_eq (j p : Nat) : invLinearG j p =
    (mulBits 0x0e j).map (fun t => 128 * (0 + t) + invSrc (down p 0)) ++
      ((mulBits 0x0b j).map (fun t => 128 * (0 + t) + invSrc (down p 1)) ++
      ((mulBits 0x0d j).map (fun t => 128 * (0 + t) + invSrc (down p 2)) ++
      ((mulBits 0x09 j).map (fun t => 128 * (0 + t) + invSrc (down p 3)) ++
    ((mulBits 0x0e j).map (fun t => 128 * (8 + t) + down p 0) ++
      ((mulBits 0x0b j).map (fun t => 128 * (8 + t) + down p 1) ++
      ((mulBits 0x0d j).map (fun t => 128 * (8 + t) + down p 2) ++
      (mulBits 0x09 j).map (fun t => 128 * (8 + t) + down p 3))))))) := by
  simp [invLinearG, invMcWords, List.map_map, Function.comp_def]

/-- A byte of `InvMixColumns` after `AddRoundKey`, from key bytes XORed with `{63}`. -/
theorem imc63 (a k : Nat → Byte) :
    Spec.Aes.mul 0x0e (a 0) ^^^ (Spec.Aes.mul 0x0b (a 1) ^^^ (Spec.Aes.mul 0x0d (a 2) ^^^ (Spec.Aes.mul 0x09 (a 3) ^^^
      (Spec.Aes.mul 0x0e (k 0 ^^^ 0x63) ^^^ (Spec.Aes.mul 0x0b (k 1 ^^^ 0x63) ^^^
        (Spec.Aes.mul 0x0d (k 2 ^^^ 0x63) ^^^ Spec.Aes.mul 0x09 (k 3 ^^^ 0x63))))))) =
    (Spec.Aes.mul 0x0e (a 0 ^^^ k 0) ^^^ Spec.Aes.mul 0x0b (a 1 ^^^ k 1) ^^^ Spec.Aes.mul 0x0d (a 2 ^^^ k 2) ^^^
      Spec.Aes.mul 0x09 (a 3 ^^^ k 3)) ^^^ 0x63 := by
  have e : ∀ c : Nat, c = 0x0e ∨ c = 0x0b ∨ c = 0x0d ∨ c = 0x09 → ∀ x y : Byte,
      Spec.Aes.mul (BitVec.ofNat 8 c) (x ^^^ y) = Spec.Aes.mul (BitVec.ofNat 8 c) x ^^^ Spec.Aes.mul (BitVec.ofNat 8 c) y :=
    fun c hc x y => mul_xor hc x y
  have e0 : ∀ x y : Byte, Spec.Aes.mul 0x0e (x ^^^ y) = Spec.Aes.mul 0x0e x ^^^ Spec.Aes.mul 0x0e y := e 0x0e (by decide)
  have e1 : ∀ x y : Byte, Spec.Aes.mul 0x0b (x ^^^ y) = Spec.Aes.mul 0x0b x ^^^ Spec.Aes.mul 0x0b y := e 0x0b (by decide)
  have e2 : ∀ x y : Byte, Spec.Aes.mul 0x0d (x ^^^ y) = Spec.Aes.mul 0x0d x ^^^ Spec.Aes.mul 0x0d y := e 0x0d (by decide)
  have e3 : ∀ x y : Byte, Spec.Aes.mul 0x09 (x ^^^ y) = Spec.Aes.mul 0x09 x ^^^ Spec.Aes.mul 0x09 y := e 0x09 (by decide)
  have h63 : Spec.Aes.mul 0x0e 0x63 ^^^ Spec.Aes.mul 0x0b 0x63 ^^^ Spec.Aes.mul 0x0d 0x63 ^^^ Spec.Aes.mul 0x09 0x63 =
      (0x63 : Byte) := by decide +kernel
  rw [e0 (k 0), e1 (k 1), e2 (k 2), e3 (k 3), e0 (a 0), e1 (a 1), e2 (a 2), e3 (a 3)]
  conv => rhs; rw [← h63]
  ac_rfl

theorem bs_invLinear {W Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = xorBits W (invLinearG j p)) (hr : BsRel W S)
    (hk : KeyRel (fun k => W (8 + k)) rk) :
    BsRel Q' fun b => x63 (invMixColumns (addRoundKey (invShiftRows (S b)) rk)) := by
  intro b hb i hi
  have hm : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega_using [hi]
  have hs : ∀ n : Nat, n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4) < 16 := fun n => by omega_using []
  have hd : ∀ k < 4, down (pos b i) k < 128 := fun k hk => by rw [down_pos b hb i hi k hk]; exact pos_lt hb (hm k)
  have hsrc : ∀ k < 4, invSrc (down (pos b i) k) < 128 := fun k hk => by
    rw [down_pos b hb i hi k hk, invSrc_pos b hb _ (hm k)]; exact pos_lt hb (hs _)
  have hA : ∀ k < 4, bsByte (fun t => W (0 + t)) (invSrc (down (pos b i) k)) =
      (invShiftRows (S b)).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0 := fun k hk => by
    rw [down_pos b hb i hi k hk, invSrc_pos b hb _ (hm k), getD_invShiftRows _ (hm k), ← hr b hb _ (hs _)]
    simp only [Nat.zero_add]
  have hK : ∀ k < 4, bsByte (fun t => W (8 + t)) (down (pos b i) k) =
      rk.getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0 ^^^ 0x63 := fun k hk' => by
    rw [down_pos b hb i hi k hk']; exact hk b hb _ (hm k)
  rw [getD_x63 _ hi, getD_invMixColumns _ hi, getD_addRoundKey _ _ (hm 0), getD_addRoundKey _ _ (hm 1),
    getD_addRoundKey _ _ (hm 2), getD_addRoundKey _ _ (hm 3)]
  have key := imc63 (fun k => (invShiftRows (S b)).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0)
    (fun k => rk.getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0)
  rw [← key]
  refine byte_ext fun j hj => ?_
  have hlt := fun c hc => mulBits_lt c hc j hj
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), invLinearG_eq]
  simp only [xorBits_append]
  rw [xorBits_row (hsrc 0 (by decide)) (hlt 0x0e (by decide)), xorBits_row (hsrc 1 (by decide)) (hlt 0x0b (by decide)),
    xorBits_row (hsrc 2 (by decide)) (hlt 0x0d (by decide)), xorBits_row (hsrc 3 (by decide)) (hlt 0x09 (by decide)),
    xorBits_row (hd 0 (by decide)) (hlt 0x0e (by decide)), xorBits_row (hd 1 (by decide)) (hlt 0x0b (by decide)),
    xorBits_row (hd 2 (by decide)) (hlt 0x0d (by decide)), xorBits_row (hd 3 (by decide)) (hlt 0x09 (by decide)),
    hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 3 (by decide), hK 0 (by decide), hK 1 (by decide),
    hK 2 (by decide), hK 3 (by decide)]
  simp only [BitVec.getLsbD_xor, mul0e_bit _ hj, mul0b_bit _ hj, mul0d_bit _ hj, mul09_bit _ hj]


/-! ### The layers, on the machine -/

theorem invShift_invSub (x : Spec.Aes.State) : invShiftRows (invSubBytes x) = invSubBytes (invShiftRows x) :=
  st_ext fun i hi => by
    rw [getD_invShiftRows _ hi, getD_invSubBytes _ (by omega_using []), getD_invSubBytes _ hi, getD_invShiftRows _ hi]

theorem invSbox_keeps : (invSboxCode.all fun i => i.dst == none) = true := by decide +kernel
theorem invLinear_keeps : (invLinear.all fun i => i.dst == none) = true := by decide +kernel
theorem invToBs_keeps : (invToBs.all fun i => i.dst == none || i.dst == some .eax) = true := by decide +kernel
theorem invFromBs_keeps : (invFromBs.all fun i => i.dst == none || i.dst == some .eax) = true := by decide +kernel

theorem row_inTs63 {c : Nat} (hc : c < 256) : row inTs63 c = BitVec.ofNat 8 c ^^^ 0x63 := by
  refine row_ext fun j hj => ?_
  simp only [inTs63, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT63, Nat.testBit_xor, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, hj, compl_bit hc]

/-- The inverse S-box, at every bit position of the words in slots `0 … 7`. -/
theorem invSbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 128, (Q s' j).getLsbD p = (invSbox (bsByte (Q s) p ^^^ 0x63)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.gpr r = s.gpr r) ∧ Frame [slotsR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ invSbox_check
  have hout : ∀ j < 8, e'.slot j = some ((invSboxT inTs63).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 128, ∃ s', runBlock isa invSboxCode s = some s' ∧
      Post (TableRel p (bsByte (Q s) p).toNat) sboxCfg e' s s'
        (fun r => (invSboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, fun k a _ h => ?_, fun j _ hj _ => ?_, fun r v h => ?_⟩ he
    · revert h; cases r <;> intro h <;> cases h
    · obtain ⟨-, h'⟩ := getD_map_range h
      split at h'
      · rename_i hk8
        cases h'
        simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
          BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, Q, sboxCfg]
      · cases h'
    · simp [sboxCfg] at hj
    · revert h; cases r <;> intro h <;> cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [sboxCfg, slots]; omega_using [hj]) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, sboxCfg, hb] at this
    rw [Q, hb, ← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, row_inTs63 hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [keep_all invSbox_keeps r]; exact Bool.noConfusion

/-! ### The rounds -/

section
variable {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}

theorem invSbox_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s)
    {T : Nat → Spec.Aes.State} (hbs : BsRel (Q s) fun b => x63 (T b)) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → (∀ r, s'.gpr r = s.gpr r) →
      BsRel (Q s') (fun b => invSubBytes (T b)) → WP isa (.block rest) s' P) :
    WP isa (.block (invSboxCode ++ rest)) s P := by
  obtain ⟨s', hs', hq, hrd, hwr, hgp, hf⟩ := invSbox_ok (hg.sboxOk he)
  rw [hg.slotsR] at hf
  exact split_run ⟨s', hs', h s' (hg.step he hrd hwr (fun r _ _ _ => hgp r) hf) hgp (bs_invSub hq hbs)⟩

/-- The rest of a round, from the inverse S-box. -/
theorem invLinear_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {m : Nat}
    (hm : m < R - 1) (hk : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * m)) {T : Nat → Spec.Aes.State}
    (hbs : BsRel (Q s) T) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → (∀ r, s'.gpr r = s.gpr r) →
      BsRel (Q s') (fun b => x63 (invMixColumns (addRoundKey (invShiftRows (T b)) (roundKey w (m + 1))))) →
      WP isa (.block rest) s' P) :
    WP isa (.block (invLinear ++ rest)) s P := by
  obtain ⟨s', hs', hq, hrd, hwr, hgp, hf⟩ := round_layer (c := roundCfg) rfl rfl invLinear_check
    (hg.roundOk he hm hk) (by decide) (roundW s) (fun k hk => roundW_lt hk) (fun k _ => roundW_key k)
    (keep_all invLinear_keeps _)
  rw [hg.slotsR] at hf
  have hgp' : ∀ r, s'.gpr r = s.gpr r := fun r => hgp r (keep_all invLinear_keeps r)
  refine split_run ⟨s', hs', h s' (hg.step he hrd hwr (fun r _ _ _ => hgp' r) hf) hgp'
    (bs_invLinear (W := roundW s) (S := T) (fun j hj p hp => ?_)
      (bsRel_congr hbs fun j hj => roundW_lt hj) (keyRel_congr (hg.keys m hm) fun k _ => ?_))⟩
  · rw [hq j hj p hp, Nat.zero_testBit, Bool.false_xor]
  · rw [roundW_key, hk, xAddr, addr_add]

/-- A middle round of the inverse cipher. -/
theorem invRound_ok (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s) {m : Nat}
    (hm : m < R - 1) (hk : s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (R - 1 - m)))
    (hn : s.gpr .eax = BitVec.ofNat 32 (R - 1 - m)) {T : Nat → Spec.Aes.State}
    (hbs : BsRel (Q s) fun b => x63 (T b)) :
    WP isa (.block invRoundBody) s fun s' => RGood rd wr B S E R w s₀ s' ∧
      s'.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (R - 1 - (m + 1))) ∧
      s'.gpr .eax = BitVec.ofNat 32 (R - 1 - (m + 1)) ∧
      BsRel (Q s') (fun b => x63 (irnd R w m (T b))) ∧ s'.zf = some (decide (m + 1 = R - 1)) := by
  have hR := he.hR
  simp only [invRoundBody, List.append_assoc]
  refine wp_subi fun s₁ u₁ _ _ => ?_
  have h₁ := hg.upd he u₁ (by decide)
  have hk₁ : s₁.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (R - 1 - (m + 1))) := by
    rw [u₁.gpr, hk, show keysOff + 128 * (R - 1 - m) = keysOff + 128 * (R - 1 - (m + 1)) + 128 by omega_using [hm],
      BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  have hq₁ : Q s₁ = Q s := Q_congr (u₁.other _ (by decide)) u₁.mem
  refine invSbox_wp he h₁ (by rw [hq₁]; exact hbs) fun s₂ h₂ g₂ hbs₂ =>
    invLinear_wp he h₂ (m := R - 1 - (m + 1)) (by omega_using [hm]) (by rw [g₂, hk₁]) hbs₂ fun s₃ h₃ g₃ hbs₃ =>
    wp_subi fun s₄ u₄ _ hz => WP.block_nil ?_
  have hax : s₃.gpr .eax = BitVec.ofNat 32 (R - 1 - m) := by rw [g₃, g₂, u₁.other _ (by decide), hn]
  have hsub : BitVec.ofNat 32 (R - 1 - m) - 1 = BitVec.ofNat 32 (R - 1 - (m + 1)) :=
    Wp.sub_ofNat (b := 1) (by omega_using [hm])
  refine ⟨h₃.upd he u₄ (by decide), by rw [u₄.other _ (by decide), g₃, g₂, hk₁], by rw [u₄.gpr, hax, hsub], ?_, ?_⟩
  · rw [Q_congr (s := s₃) (u₄.other _ (by decide)) u₄.mem]
    intro b hb i hi
    rw [hbs₃ b hb i hi]
    simp only [irnd, invShift_invSub, show R - 1 - (m + 1) + 1 = R - 1 - m by omega_using [hm]]
  · rw [hz, hax, hsub, ofNat_beq_zero (by omega_using [hR])]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hm], fun h => by omega_using [h]⟩)

/-- `kp :=` the end of the round keys, and `eax :=` how many there are. -/
theorem invRoundsStart_wp (he : Env rd wr B S E R) {s₀ : State} {s : State} (hg : RGood rd wr B S E R w s₀ s)
    {P : State → Prop}
    (h : ∀ s', RGood rd wr B S E R w s₀ s' → s'.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (R - 1)) →
      s'.gpr .eax = BitVec.ofNat 32 (R - 1) → Q s' = Q s → P s') : WP isa (.block invRoundsStart) s P := by
  have hR := he.hR
  refine wp_ldm (B := E) (o := 8) hg.good.esp (hg.argIn he (i := 1) (by decide)) fun s₁ u₁ => ?_
  have h₁ := hg.upd he u₁ (by decide)
  refine wp_ldm (B := E) (o := 8) h₁.good.esp (h₁.argIn he (i := 1) (by decide)) fun s₂ u₂ => ?_
  have h₂ := h₁.upd he u₂ (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => wp_add fun s₆ u₆ _ =>
    wp_add fun s₇ u₇ _ => wp_add fun s₈ u₈ _ => wp_add fun s₉ u₉ _ => ?_
  have h₉ := ((((((h₂.upd he u₃ (by decide)).upd he u₄ (by decide)).upd he u₅ (by decide)).upd he u₆ (by decide)).upd he
    u₇ (by decide)).upd he u₈ (by decide)).upd he u₉ (by decide)
  refine wp_add fun s₁₀ u₁₀ _ => wp_addi fun s₁₁ u₁₁ => wp_subi fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have h₁₂ := ((h₉.upd he u₁₀ (by decide)).upd he u₁₁ (by decide)).upd he u₁₂ (by decide)
  have e₉ : s₉.gpr kp = BitVec.ofNat 32 (128 * R) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.other kp (by decide), u₁.gpr, hg.good.arg1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  refine h s₁₂ h₁₂ ?_ ?_ (Q_congr (by rw [h₁₂.good.edi, hg.good.edi])
    (by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]))
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, e₉, show s₉.gpr sb = B from h₉.good.edi,
      BitVec.add_comm (BitVec.ofNat 32 (128 * R)) B, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 128 * R + (keysOff - 128) = keysOff + 128 * (R - 1) by simp only [keysOff]; omega_using [hR]]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, h₁.good.arg1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Wp.sub_ofNat (by omega_using [hR])]

/-- Eight blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt8_ok (he : Env rd wr B S E R) {s₀ : State} (hg₀ : Good rd wr B S E R w s₀)
    (hk₀ : KeysAt s₀.mem B w (R - 1)) {T : Nat → Spec.Aes.State} (hin : InRel (Q s₀) T) :
    WP isa decrypt8 s₀ fun s => RGood rd wr B S E R w s₀ s ∧
      InRel (Q s) (fun b => Spec.Aes.invCipher R w (T b)) := by
  have hR := he.hR
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (T b) (roundKey w R)
  have hg : RGood rd wr B S E R w s₀ s₀ := ⟨hg₀, Frame.refl _ _, hk₀, fun _ _ _ _ => rfl⟩
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m < R - 1 ∧ RGood rd wr B S E R w s₀ s ∧
    s.gpr kp = B + BitVec.ofNat 32 (keysOff + 128 * (R - 1 - m)) ∧ s.gpr .eax = BitVec.ofNat 32 (R - 1 - m) ∧
    BsRel (Q s) (fun b => x63 (invMid R w m (A b)))
  let Mid : State → Prop := fun s => RGood rd wr B S E R w s₀ s ∧ BsRel (Q s) (fun b => x63 (invMid R w (R - 1) (A b)))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- The last round key, and bitsliced.
    simp only [List.append_assoc]
    refine wp_ldm (B := E) (o := 4) hg.good.esp (hg.argIn he (i := 0) (by decide)) fun s₁ u₁ => ?_
    have h₁ := hg.upd he u₁ (by decide)
    have hq₁ : Q s₁ = Q s₀ := Q_congr (u₁.other _ (by decide)) u₁.mem
    refine lastKeyPtr_wp he h₁ (by rw [u₁.gpr]; exact hg₀.arg0) fun s₂ h₂ hc₂ hq₂ => ?_
    refine key_layer he h₂ (j := R) (Nat.le_refl _) hc₂ invToBs_check invToBs_keeps
      fun s₃ h₃ g₃ ⟨W, hW, hrk, hq₃⟩ => ?_
    have hbs₃ : BsRel (Q s₃) fun b => x63 (A b) := bs_invToBs (W := W) hq₃
      (fun b hb i hi j hj => by rw [hW b hb, hq₂, hq₁]; exact hin b hb i hi j hj) hrk
    exact invRoundsStart_wp he h₃ fun s₄ h₄ hk₄ hn₄ hq₄ =>
      ⟨0, rfl, by omega_using [hR], h₄, hk₄, hn₄, by rw [hq₄]; exact hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hg, hk, hn, hbs⟩ := hs
    refine WP.mono (invRound_ok he hg hm hk hn hbs) fun s' ⟨hg', hk', hn', hbs', hz⟩ => ?_
    by_cases hlast : m + 1 = R - 1
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hg', ?_⟩
      rw [← hlast]
      intro b hb i hi
      rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega_using [hm], m + 1, rfl,
        by omega_using [hm, hlast], hg', hk', hn', fun b hb i hi => by
          rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hg, hbs⟩ := h
    simp only [List.append_assoc]
    refine invSbox_wp he hg hbs fun s₁ h₁ g₁ hbs₁ => ?_
    refine wp_ldm (B := E) (o := 4) h₁.good.esp (h₁.argIn he (i := 0) (by decide)) fun s₂ u₂ => ?_
    have h₂ := h₁.upd he u₂ (by decide)
    have hq₂ : Q s₂ = Q s₁ := Q_congr (u₂.other _ (by decide)) u₂.mem
    rw [← List.append_nil invFromBs]
    refine key_layer he h₂ (j := 0) (Nat.zero_le _) (by rw [u₂.gpr, show s₁.mem.readW (addr E 4) 32 = S from h₁.good.arg0]; simp)
      invFromBs_check invFromBs_keeps fun s₃ h₃ _ ⟨W, hW, hrk, hq₃⟩ => WP.block_nil ⟨h₃, ?_⟩
    have := bs_invFromBs (W := W) (T := fun b => invSubBytes (invMid R w (R - 1) (A b)))
      (fun j hj p hp => by rw [hq₃ j hj p hp]; simp) (bsRel_congr hbs₁ fun j hj => by rw [hW j hj, hq₂]) hrk
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invShift_invSub, invCipher_eq]; rfl

end

end VG.Proof.Aes.X86.Sse
