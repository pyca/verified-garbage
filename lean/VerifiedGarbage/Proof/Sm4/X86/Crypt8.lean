import VerifiedGarbage.Proof.Sm4.X86.Core
import VerifiedGarbage.Proof.Sm4.Layout

/-!
# The transposes, and eight blocks of bitsliced SM4 on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Crypt8.lean`): `toBs_step` turns the eight
blocks of the tail buffer into the state's planes, `fromBs_step` turns the
state's planes back into the output blocks (the words in reverse order),
and `crypt8_wp` composes them with the 32 rounds (`rounds_wp`).
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Bitslice (bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Sm4 (quads ofBlock outBlock getLsbD_wordAt getLsbD_outBlock' blockAt_getD)

/-- Bit `8 i + t` of a little-endian 32-bit word is bit `t` of its byte `i`. -/
theorem readW32_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 4) (ht : t < 8) :
    (m.readW a 32).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 32 by omega]

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem ((s.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := by
    simp only [bsCfg, tableSlot_eq] at hk ⊢
    rw [hc.wr, hc.base]; exact hp.scr.slot (by rw [slots_eq]; omega)
  extIn k hk := by simp [bsCfg] at hk
  fit := by have := hp.scr.fit; simp only [bsCfg, hc.base]; rw [slots_eq] at this; rw [tableSlot_eq]; omega
  sep k _ j hj := by simp [bsCfg] at hj

/-- A block of the slots below the table that writes only the layers'
registers keeps `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 _ => hk r h1) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base])

theorem byte_addr (b : BitVec 32) {k i n : Nat} (hn : 4 * k + i = n) (hfit : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k + BitVec.ofNat 64 i = b.setWidth 64 + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_eq hfit, VG.Offset.add_add, hn]

theorem writes_tmp {is : List Instr} (h : ([Reg.esp, .esi, .edi].all fun r => is.all fun i => i.dst != some r) = true)
    (r : Reg) (hr : r ∉ tmpRegs) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp h r (not_tmp r hr)

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hfit := hp.scr.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', hso, rd', wr', o', f'⟩ := linear_ok toBs_check (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun j i hji hj => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by omega, rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hso
  have hk : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (writes_tmp (by decide +kernel) r hr)
  have hb' : s'.gpr sb = s.gpr sb := hk _ (by decide)
  refine ⟨s', h', hc.bs rd' wr' hk f', fun w hw b hb i hi j hj => ?_⟩
  have hp8 : 8 * i + b < 32 := by omega
  have hmem := hso (32 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
      simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega, rfl⟩) _ hp8
  rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega] at hmem
  have ht : 8 * i + j < 32 := by omega
  show (slotW s' (stateSlot w j)).getLsbD (8 * i + b) = _
  rw [slotW, hb', show stateSlot w j = 32 + (8 * w + j) by simp only [stateSlot]; omega, hmem, toBsG,
    show (8 * i + b) % 8 = b by omega, show (8 * i + b) / 8 = i by omega, xorBits_cons, xorBits_nil,
    Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW32_bit _ _ hi hj]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega), byte_addr _ rfl (by rw [tailSlot_eq]; omega),
    VG.Offset.add_add, show 4 * (tailSlot + (4 * b + w)) + i = 4 * tailSlot + 16 * b + (4 * w + i) by omega]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 8, tailBlock s' b = outBlock (X b) := by
  have hfit := hp.scr.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', hso, rd', wr', o', f'⟩ := linear_ok fromBs_check (ok_bs hp hc)
    (fun i => slotW s (32 + i))
    (fun j i hji hj => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by omega, by simp only [Nat.zero_add]; rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hso
  have hk : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (writes_tmp (by decide +kernel) r hr)
  have hb' : s'.gpr sb = s.gpr sb := hk _ (by decide)
  refine ⟨s', h', hc.bs rd' wr' hk f', hk _ (by decide), fun w hw => (hX w hw).congr fun j hj => ?_,
    fun b hb => ?_⟩
  · show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
    rw [slotW, hb', show stateSlot w j = 32 + (8 * w + j) by simp only [stateSlot]; omega]
    exact keep_word (W := fun i => slotW s (32 + i)) (i := 0 + (8 * w + j)) (by simp)
      (hso _ _ (List.mem_append_right _ (stateKeep_mem (x := 0) (a := 4) (by omega) (by omega))))
  apply Vector.ext
  intro k hk
  refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
  rw [getLsbD_outBlock' (X b) hk hj]
  have ht : 8 * (k % 4) + j < 32 := by omega
  have hmem := hso (tailSlot + (4 * b + k / 4)) (fromBsG (4 * b + k / 4)) (List.mem_append_left _ (by
      simp only [List.mem_map, List.mem_range]; exact ⟨4 * b + k / 4, by omega, rfl⟩)) _ ht
  rw [readW32_bit _ _ (by omega) hj, byte_addr _ rfl (by rw [tailSlot_eq]; omega)] at hmem
  have e1 : 8 * (3 - (4 * b + k / 4) % 4) + (8 * (k % 4) + j) % 8 = 8 * (3 - k / 4) + j := by omega
  have e2 : 8 * ((8 * (k % 4) + j) / 8) + (4 * b + k / 4) / 4 = 8 * (k % 4) + b := by omega
  have hw : 3 - k / 4 < 4 := by omega
  have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega) j hj
  rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega)] at hmem
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
  rw [hb', VG.Offset.add_add,
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

end VG.Proof.Sm4.X86
