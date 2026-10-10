import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Framework.Arm.Bytes

/-!
# The transposes, and eight blocks of bitsliced SM4 on ARMv7

`toBs_step` turns the eight blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt8_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR)
open VG.Proof.Sm4 (quads ofBlock outBlock getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := by
    simp only [bsCfg, tableSlot_eq] at hk ⊢
    rw [hc.wr, hc.base]; exact slot_in hp.scr hp.fit (by rw [slots_eq]; omega)
  extIn k hk := by simp [bsCfg] at hk
  slots := by have := hp.fit; simp only [bsCfg, hc.base]; rw [slots_eq] at this; rw [tableSlot_eq]; omega
  sep k _ j hj := by simp [bsCfg] at hj

/-- The registers `Ctx` keeps but `kp`: `sb` alone. -/
theorem keep_sb (r : Reg) (h1 : r ∉ layerWrites) (h2 : r ≠ kp) : r = sb := by
  revert h1 h2; cases r <;> decide

/-- A block of the slots below the table that keeps `sb` keeps `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h1 h2 => by rw [keep_sb r h1 h2]; exact hb) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base])

theorem byte_addr (b : BitVec 32) {k i n : Nat} (hn : 4 * k + i = n) (hfit : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k + BitVec.ofNat 64 i = State.addr b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add hfit, BitVec.add_assoc, ← BitVec.ofNat_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, -, rd', wr', sp', -, f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega, by omega, rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', fun w hw b hb i hi j hj => ?_⟩
  have hp8 : 8 * i + b < 32 := by omega
  have hmem := hso (32 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
      simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega, rfl⟩)
      (by rw [tableSlot_eq]; omega) _ hp8
  rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega] at hmem
  have ht : 8 * i + j < 32 := by omega
  show (slotW s' (stateSlot w j)).getLsbD (8 * i + b) = _
  rw [slotW, hb', show stateSlot w j = 32 + (8 * w + j) by simp only [stateSlot]; omega, hmem, toBsG,
    show (8 * i + b) % 8 = b by omega, show (8 * i + b) / 8 = i by omega, xorBits_cons, xorBits_nil,
    Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW_bit _ _ hi hj]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega), byte_addr _ rfl (by rw [tailSlot_eq]; omega),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (tailSlot + (4 * b + w)) + i = 4 * tailSlot + 16 * b + (4 * w + i) by omega]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 8, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, hkeep, rd', wr', sp', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (32 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega, by omega, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkeep
  have hall : (fromBs.all fun i => dstOf i != some kp) = true := by decide +kernel
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', o' kp hall, fun w hw => (hX w hw).congr fun j hj => ?_, fun b hb => ?_⟩
  · show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
    have hm : stateSlot w j ∈ stateSlots := by
      simp only [stateSlots, List.mem_map, List.mem_range]
      exact ⟨8 * w + j, by omega, by simp only [stateSlot]; omega⟩
    rw [slotW, hb', hkeep _ hm (by simp only [stateSlot, tableSlot_eq]; omega)]
  apply Vector.ext
  intro k hk
  refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
  rw [getLsbD_outBlock' (X b) hk hj]
  have ht : 8 * (k % 4) + j < 32 := by omega
  have hmem := hso (tailSlot + (4 * b + k / 4)) (fromBsG (4 * b + k / 4)) (by
      simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + k / 4, by omega, rfl⟩)
      (by rw [tableSlot_eq, tailSlot_eq]; omega) _ ht
  rw [readW_bit _ _ (by omega) hj, byte_addr _ rfl (by rw [tailSlot_eq]; omega)] at hmem
  have e1 : 8 * (3 - (4 * b + k / 4) % 4) + (8 * (k % 4) + j) % 8 = 8 * (3 - k / 4) + j := by omega
  have e2 : 8 * ((8 * (k % 4) + j) / 8) + (4 * b + k / 4) / 4 = 8 * (k % 4) + b := by omega
  have hw : 3 - k / 4 < 4 := by omega
  have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega) j hj
  rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega)] at hmem
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
  rw [hb', BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * tailSlot + 16 * b + k = 4 * (tailSlot + (4 * b + k / 4)) + k % 4 by omega,
    hmem, ← hbit, planes_eq]

/-- `crypt8`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt8_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, X₁⟩ := toBs_step hp (Ctx.refl s₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.Arm
