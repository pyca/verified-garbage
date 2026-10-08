import VerifiedGarbage.Proof.Camellia.X86_64.Prologue

/-!
# A group of blocks of Camellia ECB on x86-64

`group_wp`: one iteration of the data loop copies the group's blocks (eight,
or the last one to seven) to the tail buffer, saves the data pointer, the
blocks left and the postwhitening's address in their slots, transforms the
tail buffer (`crypt8_ok`), reloads them, copies the blocks back and steps
to the next group.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)

/-! ## Small blocks -/

theorem cmpImm_ok (s : State) (r : Reg) (k : BitVec 32) {v K : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) :
    ∃ s', runBlock isa [.alu .cmp r (.imm k)] s = some s' ∧ s'.cf = some (decide (v < K)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r - k.signExtend 64) (decide ((s.gpr r).toNat < (k.signExtend 64).toNat))
    (subOverflow (s.gpr r) (k.signExtend 64) (s.gpr r - k.signExtend 64)), ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)]

theorem movR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [movR d r] s = some s' ∧ s'.gpr d = s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.gpr r), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' hr => by simp only [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl⟩
  simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]

/-- `rcx := min(r8, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r8 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v 8) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := movImm_ok s .rcx 8
  obtain ⟨s₂, e₂, f₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 8 (v := v) (by rw [o₁ _ (by decide), hr]) hv rfl
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([Instr.movImm64 .rcx 8, .alu .cmp .r8 (.imm 8)] : List Instr) =
      [.movImm64 .rcx 8] ++ [.alu .cmp .r8 (.imm 8)] from rfl, runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.ite (decide (v < 8)) (by simp [X86_64.eval, f₂]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rcx .r8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => ?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [r₃, g₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega)]
    · rw [o₃ r hr, g₂, o₁ r hr]
  · refine WP.of_runBlock ⟨s₂, rfl, ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [g₂, c₁, Nat.min_eq_right (by simp at h; omega)]; rfl
    · rw [g₂, o₁ r hr]

/-- `mov [sb + 8 k], r`. -/
theorem stReg_ok {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [st k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' : InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := hw
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr r) }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [st, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, State.ea, ofInt_nat, hb, hw', ite_true]

/-- `mov d, [sb + 8 k]`. -/
theorem movS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [movS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * k)) 8 := hr
  refine ⟨s.setReg d (slotW s k), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [movS, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.ea, ofInt_nat, hb, hr', ite_true, Option.map_some, slotW, wordAddr]

/-- `tailAddr r`. -/
theorem tailAddr_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa (tailAddr r) s = some s' ∧ s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s r sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ r (BitVec.ofNat 32 (8 * tailSlot))
  refine ⟨s₂, by rw [tailAddr, show ([movR r sb, .alu .add r (.imm (BitVec.ofNat 32 (8 * tailSlot)))] :
      List Instr) = [movR r sb] ++ [.alu .add r (.imm (BitVec.ofNat 32 (8 * tailSlot)))] from rfl,
      runBlock_append', e₁, Option.bind_some, e₂], ?_, fun r' h => by rw [o₂ r' h, o₁ r' h],
    by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [r₂, r₁]; rfl

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ layerMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ i < 8 * g + 2, EntryOk m b i (E i)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–52, 96–367 and 371–376. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 40⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * 272⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 48⟩]

theorem ScrOk.frame {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b g E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega) (by omega))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * keySlot + 64 * i + 8 * j) (VG.Offset.sub b (by omega) (by rw [keySlot_eq]; omega))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i)) (VG.Offset.sub b (by omega) (by omega))

end VG.Proof.Camellia.X86_64
