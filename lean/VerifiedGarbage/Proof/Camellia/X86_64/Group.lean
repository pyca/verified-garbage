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

theorem dataSlot_eq : dataSlot = 369 := rfl
theorem countSlot_eq : countSlot = 370 := rfl
theorem savedSlot_eq : savedSlot = 371 := rfl

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

theorem subSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.reg r)] s = some s' ∧ s'.zf = some true ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr r - s.gpr r) ((s.gpr r).toNat < (s.gpr r).toNat)
    (subOverflow (s.gpr r) (s.gpr r) (s.gpr r - s.gpr r))).setReg r (s.gpr r - s.gpr r), ?_, ?_,
    fun r' hr => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_setReg, RegUpd.zf_arithFlags, BitVec.sub_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega)

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

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b g E m' := by
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * keySlot + 64 * i + 8 * j) (VG.Offset.sub b (by omega) (by rw [keySlot_eq]; omega))
  · rw [← h.saved i hi]
    have : savedSlot = 371 := rfl
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i)) (VG.Offset.sub b (by omega) (by omega))

/-! ## The data loop -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Camellia.Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n g : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4

/-- `copyBlocks` from `rax` to `rbx`, `rcx` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .rax = X) (hy : s.gpr .rbx = Y) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- Each block, transformed. -/
def outF (m₀ : Mem) (D : Addr) (g : Nat) (E : Nat → BitVec 64) (j : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock
    (Spec.Camellia.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (128 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 8 * k)
  lt : 8 * k < n
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n (8 * k) (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- A word written inside `R`. -/
theorem frame_writeW {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h => hx R (List.mem_singleton_self _) (hs x (by simp only [Region.Contains]; omega))

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Camellia.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Camellia.blockAt, Vector.getD, hi]

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem toNat_off (b : Addr) {d : Nat} (h : b.toNat + d < 2 ^ 64) : (b + BitVec.ofNat 64 d).toNat = b.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.X86_64.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n g E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  rw [slots_eq] at hfit
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < c := by omega
  have hc8 : c ≤ 8 := by omega
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (128 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t, t < 16 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
  have inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega))
  have inSlot : ∀ j < slots, InRegions s.wr (wordAddr b j) 8 := fun j hj =>
    ⟨_, hwS, VG.Offset.contains_base b (by rw [slots_eq] at hj ⊢; omega) (by rw [slots_eq] at hj; omega)⟩
  unfold Impl.Camellia.X86_64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r8 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .rax .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := tailAddr_ok s₂a .rbx
  have base₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide), hi.base]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂ r h2, o₂a r h1, o₁ r h3]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₂a, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc8
    (by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide), hi.rdx])
    (by rw [r₂, o₂a _ (by decide), o₁ _ (by decide), hi.base])
    (by rw [o₂ _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  have base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), base₂]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  have g₃' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3]
  have sc₃ : ScrOk s₀ b g E s₃.mem := by
    refine hi.scr.frame hg4 (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b (Or.inl ?_) ?_ ?_ <;>
      (try simp only [tailSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega
  -- The state to its slots, and `rdx` to the tail buffer.
  have inS₃ : ∀ j < slots, InRegions s₃.wr (wordAddr b j) 8 := fun j hj => by rw [wr₃']; exact inSlot j hj
  have hds : dataSlot < slots := by rw [dataSlot_eq, slots_eq]; decide
  have hcs : countSlot < slots := by rw [countSlot_eq, slots_eq]; decide
  have hes : endSlot < slots := by rw [endSlot_eq, slots_eq]; decide
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := stReg_ok (k := dataSlot) .rdx base₃ (inS₃ _ hds)
  obtain ⟨s₄b, e₄b, m₄b, g₄b, rd₄b, wr₄b⟩ := stReg_ok (k := countSlot) .r8 (by rw [g₄a, base₃])
    (by rw [wr₄a]; exact inS₃ _ hcs)
  obtain ⟨s₄c, e₄c, m₄c, g₄c, rd₄c, wr₄c⟩ := stReg_ok (k := endSlot) .rdi (by rw [g₄b, g₄a, base₃])
    (by rw [wr₄b, wr₄a]; exact inS₃ _ hes)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := tailAddr_ok s₄c .rdx
  have base₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), g₄c, g₄b, g₄a, base₃]
  have rdx₄ : s₄.gpr .rdx = T := by rw [r₄, g₄c, g₄b, g₄a, base₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄c, wr₄b, wr₄a, wr₃']
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₄c, rd₄b, rd₄a, rd₃']
  have mem₄ : s₄.mem = ((s₃.mem.writeW (wordAddr b dataSlot) (s₃.gpr .rdx)).writeW (wordAddr b countSlot)
      (s₃.gpr .r8)).writeW (wordAddr b endSlot) (s₃.gpr .rdi) := by
    rw [m₄, m₄c, m₄b, m₄a, g₄b, g₄a]
  have f₄ : Frame [⟨b + BitVec.ofNat 64 (8 * endSlot), 24⟩] s₃.mem s₄.mem := by
    rw [mem₄]
    refine ((frame_writeW _ ?_).trans (frame_writeW _ ?_)).trans (frame_writeW _ ?_) <;>
      exact VG.Offset.sub b (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega)
        (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega)
  have slot₄ : ∀ j < slots, slotW s₄ j = if j = endSlot then s.gpr .rdi else if j = countSlot then
      s.gpr .r8 else if j = dataSlot then s.gpr .rdx else slotW s₃ j := fun j hj => by
    simp only [slotW, base₄, base₃, mem₄]
    rw [readW_slot_write _ hj hes, readW_slot_write _ hj hcs, readW_slot_write _ hj hds]
    rw [g₃' .rdi (by decide) (by decide) (by decide) (by decide), g₃' .r8 (by decide) (by decide) (by decide)
      (by decide), g₃' .rdx (by decide) (by decide) (by decide) (by decide)]
  have sc₄ : ScrOk s₀ b g E s₄.mem := by
    refine sc₃.frame hg4 f₄ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [endSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [saveState, show ([st dataSlot .rdx, st countSlot .r8, st endSlot .rdi] : List Instr) =
      [st dataSlot .rdx] ++ ([st countSlot .r8] ++ [st endSlot .rdi]) from rfl,
      runBlock_append', runBlock_append', e₄a, Option.bind_some, runBlock_append', e₄b, Option.bind_some,
      e₄c, Option.bind_some, e₄], ?_⟩)
  -- The eight blocks.
  have hcore : CorePre s₄ g E :=
    { scr := by rw [base₄, wr₄']; exact hwS
      dat := fun j hj => by rw [rdx₄, wr₄']; exact inT j hj
      sep := by rw [rdx₄, base₄]; exact VG.Offset.disjoint_base b (Nat.le_refl _) (by rw [tailSlot_eq]; omega)
      fit := by rw [base₄, slots_eq]; exact hfit
      fitD := by rw [rdx₄, toNat_off b (by rw [tailSlot_eq]; omega), tailSlot_eq]; omega
      hg := hp.hg
      nk34 := by rcases hp.hg with h | h <;> omega
      masks := sc₄.masks.ok base₄
      bound := by rw [slot₄ _ hes, ite_eq_left rfl, base₄, hi.rdi]
      keys := fun i hi' => by rw [base₄]; exact sc₄.keys i hi' }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  have rdx₅ : s₅.gpr .rdx = T := by rw [c₅.rdx, rdx₄]
  have f₅ : Frame [⟨b, 8 * keySlot⟩, ⟨T, 128⟩] s₄.mem s₅.mem := by
    have := c₅.frame; rw [base₄, rdx₄] at this; exact this
  have hT : T = b + BitVec.ofNat 64 (8 * tailSlot) := rfl
  have keepSlot : ∀ j, keySlot ≤ j → j < tailSlot → slotW s₅ j = slotW s₄ j := fun j h1 h2 => by
    simp only [slotW, base₅, base₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega) (by rw [tailSlot_eq] at h2; omega)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by omega)) (by rw [tailSlot_eq] at h2; omega)
        (by rw [tailSlot_eq]; omega)
  have sc₅ : ScrOk s₀ b g E s₅.mem := by
    refine sc₄.frame2 hg4 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl <;> rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq] <;> omega) (by rw [keySlot_eq] <;> omega)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq, tailSlot_eq] <;> omega))
        (by rw [keySlot_eq] <;> omega) (by rw [tailSlot_eq] <;> omega)
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq, savedSlot_eq] <;> omega) (by rw [savedSlot_eq] <;> omega)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq, tailSlot_eq] <;> omega))
        (by rw [savedSlot_eq] <;> omega) (by rw [tailSlot_eq] <;> omega)
  have vD : slotW s₅ dataSlot = A := by
    rw [keepSlot _ (by rw [dataSlot_eq, keySlot_eq]; omega) (by rw [dataSlot_eq, tailSlot_eq]; omega),
      slot₄ _ hds, ite_eq_right (by rw [dataSlot_eq, endSlot_eq]; omega),
      ite_eq_right (by rw [dataSlot_eq, countSlot_eq]; omega), ite_eq_left rfl, hi.rdx]
  have vC : slotW s₅ countSlot = BitVec.ofNat 64 v := by
    rw [keepSlot _ (by rw [countSlot_eq, keySlot_eq]; omega) (by rw [countSlot_eq, tailSlot_eq]; omega),
      slot₄ _ hcs, ite_eq_right (by rw [countSlot_eq, endSlot_eq]; omega), ite_eq_left rfl, hi.r8]
  have vE : slotW s₅ endSlot = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [keepSlot _ (by rw [endSlot_eq, keySlot_eq]; omega) (by rw [endSlot_eq, tailSlot_eq]; omega),
      slot₄ _ hes, ite_eq_left rfl, hi.rdi]
  -- The state back from its slots.
  have wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  have rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₄']
  have inS₅ : ∀ j < slots, InRegions (s₅.rd ++ s₅.wr) (wordAddr b j) 8 := fun j hj => by
    rw [wr₅', rd₅']; exact inRd (inSlot j hj)
  obtain ⟨s₆a, e₆a, d₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := movS_ok (k := dataSlot) .rdx base₅ (inS₅ _ hds)
  obtain ⟨s₆b, e₆b, d₆b, o₆b, m₆b, rd₆b, wr₆b⟩ := movS_ok (k := countSlot) .r8
    (by rw [o₆a _ (by decide), base₅]) (by rw [rd₆a, wr₆a]; exact inS₅ _ hcs)
  obtain ⟨s₆, e₆, d₆, o₆, m₆, rd₆, wr₆⟩ := movS_ok (k := endSlot) .rdi
    (by rw [o₆b _ (by decide), o₆a _ (by decide), base₅]) (by rw [rd₆b, wr₆b, rd₆a, wr₆a]; exact inS₅ _ hes)
  have mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆b, m₆a]
  have rdx₆ : s₆.gpr .rdx = A := by
    rw [o₆ _ (by decide), o₆b _ (by decide), d₆a, ← vD]
  have r8₆ : s₆.gpr .r8 = BitVec.ofNat 64 v := by
    rw [o₆ _ (by decide), d₆b]; simp only [slotW, m₆a, o₆a _ (by decide : sb ≠ .rdx)]; exact vC
  have rdi₆ : s₆.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [d₆]; simp only [slotW, m₆b, m₆a, o₆b _ (by decide : sb ≠ .r8), o₆a _ (by decide : sb ≠ .rdx)]; exact vE
  have base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆b _ (by decide), o₆a _ (by decide), base₅]
  have g₆ : ∀ r, r ≠ .rdx → r ≠ .r8 → r ≠ .rdi → s₆.gpr r = s₅.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h3, o₆b r h2, o₆a r h1]
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [loadState, show ([movS .rdx dataSlot, movS .r8 countSlot, movS .rdi endSlot] : List Instr) =
      [movS .rdx dataSlot] ++ ([movS .r8 countSlot] ++ [movS .rdi endSlot]) from rfl,
      runBlock_append', e₆a, Option.bind_some, runBlock_append', e₆b, Option.bind_some, e₆], ?_⟩)
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₆ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := tailAddr_ok s₇ .rax
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₈a, Option.bind_some, e₈], ?_⟩)
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆, wr₆b, wr₆a, wr₅']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆, rd₆b, rd₆a, rd₅']
  have g₈ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₈.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₈ r h2, o₈a r h1, o₇ r h3]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc8
    (by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide), base₆])
    (by rw [r₈, o₈a _ (by decide), o₇ _ (by decide), rdx₆])
    (by rw [o₈ _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  have g₉' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₉.gpr r = s₆.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₉ r h1 h2 h3 h4, g₈ r h1 h2 h3]
  have base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide), base₆]
  have rdx₉ : s₉.gpr .rdx = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide), rdx₆]
  have r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), r8₆]
  have rdi₉ : s₉.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), rdi₆]
  have rsp₉ : s₉.gpr .rsp = s₀.gpr .rsp := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide),
      c₅.keep _ (by decide) (by decide) (by decide), o₄ _ (by decide), g₄c, g₄b, g₄a,
      g₃' _ (by decide) (by decide) (by decide) (by decide), hi.rsp]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have sc₉ : ScrOk s₀ b g E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame hg4 f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [keySlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right hsub).symm
  have fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, endSlot_eq]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega)
      · exact subS (by rw [slots_eq, tailSlot_eq] <;> omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega)
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, blk s₄ j = Spec.Camellia.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [rdx₄, addr_add, addr_add, addr_add]
    have ht : 16 * j + u < 16 * c := by omega
    rw [f₄ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off b (Or.inr (by rw [endSlot_eq, tailSlot_eq]; omega)) (by rw [tailSlot_eq]; omega)
          (by decide) (by rw [endSlot_eq]; omega))]
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [this, mem₂, addr_add, hi.data _ (by omega), ite_eq_right (by omega),
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega]
  have hdata : DInv s₀.mem s₉.mem D n (8 * k + c) (outF s₀.mem D g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [addr_add, show 128 * k + (i - 128 * k) = i by omega]
      rw [e1, cp₉ _ (by omega), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega, show i % 16 = (i - 128 * k) % 16 by omega]
      have hj : (i - 128 * k) / 16 < c := by omega
      have eT : T + BitVec.ofNat 64 (i - 128 * k) = s₅.gpr .rdx + BitVec.ofNat 64 (16 * ((i - 128 * k) / 16)) +
          BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [rdx₅, addr_add, addr_add, addr_add, show 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = i - 128 * k by omega]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
      have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega)
          · exact subS (by rw [slots_eq, tailSlot_eq] <;> omega)) (by simp only; omega) hin,
        f₄.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, endSlot_eq]; omega))
          (by simp only; omega) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega))
          (by simp only; omega) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega), ite_eq_left (show i < 16 * (8 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega)]
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  unfold advance
  obtain ⟨s₁₀, e₁₀, cf₁₀, g₁₀, m₁₀, rd₁₀, wr₁₀⟩ := cmpImm_ok s₉ .r8 8 r8₉ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₁₀, e₁₀, ?_⟩)
  refine WP.ite (decide (v < 8)) (by simp [X86_64.eval, cf₁₀]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 8 := by simpa using hlt
    obtain ⟨s₁₁, e₁₁, z₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := subSelf_ok s₁₀ .r8
    refine WP.of_runBlock ⟨s₁₁, e₁₁, .inl ⟨z₁₁, ?_⟩⟩
    have hn : 8 * k + c = n := by omega
    refine ⟨by rw [o₁₁ _ (by decide), g₁₀, base₉], by rw [o₁₁ _ (by decide), g₁₀, rsp₉],
      by rw [m₁₁, m₁₀]; exact sc₉, fun i hi' => by rw [m₁₁, m₁₀, hdata i hi', hn], by rw [m₁₁, m₁₀]; exact fr,
      by rw [rd₁₁, rd₁₀, rd₉'], by rw [wr₁₁, wr₁₀, wr₉']⟩
  · have hge' : 8 ≤ v := by simpa using hge
    have hc : c = 8 := by omega
    obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addImm_ok s₁₀ .rdx 128
    obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := subImm_ok s₁₁ .r8 8
    have r8₁₁ : s₁₁.gpr .r8 = BitVec.ofNat 64 v := by rw [o₁₁ _ (by decide), g₁₀, r8₉]
    have hz : s₁₂.zf = some (decide (v = 8)) := by
      rw [z₁₂, r8₁₁, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₂, by
      rw [show ([Instr.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)] : List Instr) =
        [.alu .add .rdx (.imm 128)] ++ [.alu .sub .r8 (.imm 8)] from rfl, runBlock_append', e₁₁,
        Option.bind_some, e₁₂], ?_⟩
    have hm : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
    have base₁₂ : s₁₂.gpr sb = b := by rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, base₉]
    have rsp₁₂ : s₁₂.gpr .rsp = s₀.gpr .rsp := by rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, rsp₉]
    have rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉']
    have wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉']
    by_cases h8 : v = 8
    · refine .inl ⟨by rw [hz, h8]; rfl, base₁₂, rsp₁₂, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₂', wr₁₂'⟩
      intro i hi'
      rw [hm, hdata i hi', show 8 * k + c = n by omega]
    · refine .inr ⟨by rw [hz]; simp [h8], base₁₂, rsp₁₂, ?_, ?_, by omega, ?_, hm ▸ sc₉, ?_, hm ▸ fr,
        rd₁₂', wr₁₂'⟩
      · rw [o₁₂ _ (by decide), r₁₁, g₁₀, rdx₉, show (128 : BitVec 32).signExtend 64 = BitVec.ofNat 64 128 from rfl,
          addr_add, show 128 * k + 128 = 128 * (k + 1) by omega]
      · rw [r₁₂, r8₁₁, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
          VG.Offset.ofNat_sub_ofNat hge', show v - 8 = n - 8 * (k + 1) by omega]
      · rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, rdi₉]
      · rw [hm, show 8 * (k + 1) = 8 * k + c by omega]; exact hdata

end VG.Proof.Camellia.X86_64
