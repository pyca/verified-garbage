module

public import VerifiedGarbage.Proof.Sm4.X86_64.Group
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Sm4.X86_64.Core

/-! ### `Sm4.X86_64.Crypt16`, which this module and modules that import it used -/

section

/-!
# The transposes, and sixteen blocks of bitsliced SM4 on x86-64

`toBs_step` turns the sixteen blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt16_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)
open VG.Proof.Camellia.X86_64 (linEnvG linPostG linG_ok)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock readW64_bit getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame), h₂.masks⟩

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := ⟨_, by rw [hc.wr]; exact hp.scr, by
    have hfit := hp.fit
    simp only [bsCfg, tableSlot_eq] at hk
    simp only [wordAddr, bsCfg, hc.base]
    rw [slots_eq] at hfit ⊢
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  extIn k hk := by simp [bsCfg] at hk
  slots := by simp only [bsCfg, tableSlot_eq]; omega_arith
  sep k _ j hj := by simp [bsCfg] at hj

/-- What a block of slots below the table that keeps the masks keeps of `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem)
    (hm : MasksOk s') : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h _ => hk r h) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base]) hm

theorem byte_addr (b : Addr) {k i : Nat} {n : Nat} (hn : 8 * k + i = n) :
    wordAddr b k + BitVec.ofNat 64 i = b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_arith, by omega_arith, rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkp
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => toBs.all fun i => i.dst != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), fun w hw b hb i hi j hj => ?_⟩
  · rw [slotW, hb', hkp kv.1 (List.mem_map_of_mem hkv) (by have := mask_lt hkv; rw [tableSlot_eq]; omega_arith)]
    exact hc.masks kv hkv
  · have hp16 : 16 * i + b < 64 := by omega_arith
    have hmem := hso (64 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
        simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq]; omega_arith) _ hp16
    rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith] at hmem
    have ht : 8 * (4 * (w % 2) + i) + j < 64 := by omega_arith
    show (slotW s' (stateSlot w j)).getLsbD (16 * i + b) = _
    rw [slotW, hb', show stateSlot w j = 64 + (8 * w + j) by simp only [stateSlot]; omega_arith, hmem, toBsG,
      show (16 * i + b) % 16 = b by omega_arith, show (16 * i + b) / 16 = i by omega_arith, xorBits_cons, xorBits_nil,
      Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW64_bit _ _ (by omega_arith) hj]
    simp only [ofBlock]
    rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_arith), byte_addr _ rfl, addr_add]
    rw [show 8 * (tailSlot + (2 * b + w / 2)) + (4 * (w % 2) + i) = 8 * tailSlot + 16 * b + (4 * w + i) by omega_arith]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 16, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkp
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => fromBs.all fun i => i.dst != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega_arith
    rw [slotW, hb', hkp k hk (by rw [tableSlot_eq]; exact hk')]
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), ?_, fun b hb => ?_⟩
  · rw [keep kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hc.masks kv hkv
  · exact fun w hw => (hX w hw).congr fun j hj => by
      show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
      exact keep _ (List.mem_append_right _ (by
        simp only [stateSlots, List.mem_map, List.mem_range]
        exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩))
  · apply Vector.ext
    intro k hk
    refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
    rw [getLsbD_outBlock' (X b) hk hj]
    have ht : 8 * (k % 8) + j < 64 := by omega_arith
    have hmem := hso (tailSlot + (2 * b + k / 8)) (fromBsG (2 * b + k / 8)) (by
        simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨2 * b + k / 8, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
    rw [readW64_bit _ _ (by omega_arith) hj, byte_addr _ rfl] at hmem
    have e1 : 8 * (3 - (2 * ((2 * b + k / 8) % 2) + (8 * (k % 8) + j) / 32)) + (8 * (k % 8) + j) % 8 =
        8 * (3 - k / 4) + j := by omega_arith
    have e2 : 16 * ((8 * (k % 8) + j) / 8 % 4) + (2 * b + k / 8) / 2 = 16 * (k % 4) + b := by omega_arith
    have hw : 3 - k / 4 < 4 := by omega_arith
    have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
    rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add, show 8 * tailSlot + 16 * b + k = 8 * (tailSlot + (2 * b + k / 8)) + k % 8 by omega_arith,
      hb', hmem, ← hbit, planes_eq]

/-- `crypt16`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt16_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (hrdi : s₀.gpr .rdi = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) :
    WP isa crypt16 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 16, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, -, X₁⟩ := toBs_step hp (Ctx.refl hm)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hrdi₁ : s₁.gpr .rdi = s₁.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [c₁.keep _ (by decide) (by decide), c₁.base, hrdi]
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) c₁.masks hrdi₁ X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.GroupStep`, which only this module used -/

section

/-!
# One group of blocks of SM4 ECB on x86-64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks to
the tail buffer, transforms them there (`crypt16_wp`), copies them back and
steps to the next group.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock not_contains_off toNat_off blockAt_getD)

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.X86_64.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc16 : c ≤ 16 := by omega_arith
  obtain hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Sm4.X86_64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r8 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .rax .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := slotAddr_ok s₂a .rbx tailSlot (by decide)
  obtain base₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide), hi.base]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂ r h2, o₂a r h1, o₁ r h3]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₂a, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide), hi.rdx])
    (by rw [r₂, o₂a _ (by decide), o₁ _ (by decide), hi.base])
    (by rw [o₂ _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain g₃' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame f₃' fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  obtain hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  obtain hrdi₃ : s₃.gpr .rdi = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.rdi, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) hrdi₃) fun s₄ ⟨c₄, b₄⟩ => ?_)
  obtain base₄ : s₄.gpr sb = b := by rw [c₄.base, base₃]
  obtain f₄ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₄.mem := by have := c₄.frame; rw [base₃] at this; exact this
  obtain g₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [c₄.keep r h1 h2, g₃' r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))
      (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))]
  obtain sc₄ : ScrOk s₀ b E s₄.mem := by
    refine sc₃.frame2 f₄ (c₄.masks.at base₄) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  -- The tail buffer back to the group's blocks.
  obtain r8₄ : s₄.gpr .r8 = BitVec.ofNat 64 v := by rw [g₄ _ (by decide) (by decide), hi.r8]
  obtain rdx₄ : s₄.gpr .rdx = A := by rw [g₄ _ (by decide) (by decide), hi.rdx]
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ => ?_))
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := slotAddr_ok s₅ .rax tailSlot (by decide)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₆a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₆, by rw [runBlock_app, e₆a, Option.bind_some, e₆], ?_⟩)
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₆a, m₅]
  obtain wr₄' : s₄.wr = s.wr := by rw [c₄.wr, wr₃']
  obtain rd₄' : s₄.rd = s.rd := by rw [c₄.rd, rd₃']
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅, wr₄']
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅, rd₄']
  obtain g₆ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h2, o₆a r h1, o₅ r h3]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₆ _ (by decide), r₆a, o₅ _ (by decide), base₄])
    (by rw [r₆, o₆a _ (by decide), o₅ _ (by decide), rdx₄])
    (by rw [o₆ _ (by decide), o₆a _ (by decide), c₅])
    (fun t ht => by rw [rd₆', wr₆']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₆']; exact inA t ht) sepAT.symm) fun s₇ ⟨cp₇, f₇, g₇, rd₇, wr₇⟩ => ?_
  obtain g₇' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₇.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₇ r h1 h2 h3 h4, g₆ r h1 h2 h3]
  obtain base₇ : s₇.gpr sb = b := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), base₄]
  obtain rdx₇ : s₇.gpr .rdx = A := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), rdx₄]
  obtain r8₇ : s₇.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), r8₄]
  obtain rdi₇ : s₇.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rdi]
  obtain rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rsp]
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆', hi.wr]
  obtain rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₇ : ScrOk s₀ b E s₇.mem := by
    refine (mem₆ ▸ sc₄).frame f₇ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₇ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₇.mem := by
    refine ((f₃'.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₆ ▸ f₇).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₇.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₇ _ (by omega_arith), mem₆, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      obtain hj : (i - 256 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 256 * k) = s₄.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₄, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₄.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₄ _).getD _ 0 = _
      rw [b₄ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₇ _ hout, mem₆,
        f₄.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₇.mem := hi.frame.trans fr₇
  -- On to the next group.
  unfold advance
  obtain ⟨s₈, e₈, cf₈, g₈, m₈, rd₈, wr₈⟩ := cmpImm_ok s₇ .r8 16 r8₇ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₈, e₈, ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, cf₈]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 16 := by simpa using hlt
    obtain ⟨s₉, e₉, z₉, o₉, m₉, rd₉, wr₉⟩ := subSelf_ok s₈ .r8
    refine WP.of_runBlock ⟨s₉, e₉, .inl ⟨z₉, ?_⟩⟩
    obtain hn : 16 * k + c = n := by omega_arith
    refine ⟨by rw [o₉ _ (by decide), g₈, base₇], by rw [o₉ _ (by decide), g₈, rsp₇],
      by rw [m₉, m₈]; exact sc₇, fun i hi' => by rw [m₉, m₈, hdata i hi', hn], by rw [m₉, m₈]; exact fr,
      by rw [rd₉, rd₈, rd₇'], by rw [wr₉, wr₈, wr₇']⟩
  · have hge' : 16 ≤ v := by simpa using hge
    obtain hc : c = 16 := by omega_arith
    obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := addImm_ok s₈ .rdx 256
    obtain ⟨s₁₀, e₁₀, r₁₀, z₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subImm_ok s₉ .r8 16
    obtain r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by rw [o₉ _ (by decide), g₈, r8₇]
    obtain hz : s₁₀.zf = some (decide (v = 16)) := by
      rw [z₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₀, by
      rw [show ([Instr.alu .add .rdx (.imm 256), .alu .sub .r8 (.imm 16)] : List Instr) =
        [.alu .add .rdx (.imm 256)] ++ [.alu .sub .r8 (.imm 16)] from rfl, runBlock_app, e₉,
        Option.bind_some, e₁₀], ?_⟩
    obtain hm : s₁₀.mem = s₇.mem := by rw [m₁₀, m₉, m₈]
    obtain base₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, base₇]
    obtain rsp₁₀ : s₁₀.gpr .rsp = s₀.gpr .rsp := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rsp₇]
    obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇']
    obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇']
    by_cases h16 : v = 16
    · refine .inl ⟨by rw [hz, h16]; rfl, base₁₀, rsp₁₀, hm ▸ sc₇, ?_, hm ▸ fr, rd₁₀', wr₁₀'⟩
      intro i hi'
      rw [hm, hdata i hi', show 16 * k + c = n by omega_arith]
    · refine .inr ⟨by rw [hz]; simp [h16], base₁₀, rsp₁₀, ?_, ?_, by omega_arith, ?_, hm ▸ sc₇, ?_, hm ▸ fr,
        rd₁₀', wr₁₀'⟩
      · rw [o₁₀ _ (by decide), r₉, g₈, rdx₇, show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl,
          addr_add, show 256 * k + 256 = 256 * (k + 1) by omega_arith]
      · rw [r₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
          VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - 16 = n - 16 * (k + 1) by omega_arith]
      · rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rdi₇]
      · intro i hi'
        rw [hm, hdata i hi', show 16 * k + c = 16 * (k + 1) by omega_arith]

end VG.Proof.Sm4.X86_64

end

end


/-!
# SM4 ECB on x86-64: the whole function

`ecb_wp`: with the working space as an argument (`ecbX86_64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The specification's direction. -/
def specDir : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86-64 with its working space at `rcx`. -/
def ecbX86_64 (dir : Dir) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)) (specDir dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st setMasks)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDir ecbX86_64 crypt_eq quads ofBlock outBlock)

theorem testSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (s.gpr r == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r &&& s.gpr r) false false, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_arithFlags, BitVec.and_self]

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.X86_64.group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 16 * (k + 1), by have := d.lt; have := hk.lt; omega_arith,
      k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .r8 ∧ sreg i ≠ .rdx := by
  unfold sreg; split <;> decide

theorem prologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .rcx = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) ++ saveRegs ++
        setMasks keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r8 = s₀.gpr .rdx ∧ s.gpr .rdx = s₀.gpr .rsi ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .rcx
  obtain ⟨s₁b, e₁b, r₁b, o₁b, m₁b, rd₁b, wr₁b⟩ := movR_ok s₁a .r8 .rdx
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁b .rdx .rsi
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), o₁b _ (by decide), r₁a, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁, wr₁b, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁, wr₁b, wr₁a]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_using [this])
    (by decide)
  obtain g₁ : ∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → s₁.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [o₁ r h3, o₁b r h2, o₁a r h1]
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, show ([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) =
      [movR sb .rcx] ++ ([movR .r8 .rdx] ++ [movR .rdx .rsi]) from rfl, runBlock_app, e₁a, Option.bind_some,
      runBlock_app, e₁b, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁], by rw [g₃ _ (by decide), g₂, o₁ _ (by decide), r₁b, o₁a _ (by decide)],
    by rw [g₃ _ (by decide), g₂, r₁, o₁b _ (by decide), o₁a _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [g₃ r h4, g₂, g₁ r h1 h2 h3], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁, rd₁b, rd₁a], by rw [wr₃, wr₂, wr₁, wr₁b, wr₁a]⟩
  · obtain ⟨n1, n2, n3⟩ := sreg_ne i
    rw [← g₁ _ n1 n2 n3, ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  · have hm1 : s₁.mem = s₀.mem := by rw [m₁, m₁b, m₁a]
    rw [← hm1]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_using [])

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDir dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDir, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDir, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86_64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => gprPreserved s₀ s' ∧ (ecbX86_64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .rcx
  let D := s₀.gpr .rsi
  let n := (s₀.gpr .rdx).toNat
  let sched := s₀.gpr .rdi
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r8₁, rdx₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  obtain rdi₁ : s₁.gpr .rdi = sched := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ rdi₁ m₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  obtain hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hk₁.sched_eq' (Nat.le_refl _) f₁
  have hfitB := fitB
  rw [slots_eq] at hfitB
  obtain f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  obtain sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi])
  obtain data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  obtain fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]
  obtain r8₂ : s₂.gpr .r8 = s₀.gpr .rdx := by rw [k₂.regs _ (by decide) (by decide) (by decide), r8₁]
  obtain rdx₂ : s₂.gpr .rdx = D := by rw [k₂.regs _ (by decide) (by decide) (by decide), rdx₁]
  obtain rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ .r8
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, r8₂]
    congr 1
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [g₃, base₂], by rw [g₃, rsp₂], by rw [m₃]; exact sc₂, fun i hi => by omega,
      by rw [m₃]; exact fr₂, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨by rw [g₃, base₂], by rw [g₃, rsp₂],
      by rw [g₃, rdx₂]; simp, by rw [g₃, r8₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega_using [hn0],
      by rw [g₃, k₂.rdi], by rw [m₃]; exact sc₂, fun i hi => ?_, by rw [m₃]; exact fr₂, by rw [rd₃, rd₂],
      by rw [wr₃, wr₂]⟩
    rw [m₃, data₂ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, o₅, f₅, rd₅, wr₅⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₅ 0 (by omega_using [])
    · exact rg₅ 1 (by omega_using [])
    · rw [o₅ _ (fun i hi => by unfold sreg; split <;> decide), d₄.rsp]
    · exact rg₅ 2 (by omega_using [])
    · exact rg₅ 3 (by omega_using [])
    · exact rg₅ 4 (by omega_using [])
    · exact rg₅ 5 (by omega_using [])
  · -- The return address is untouched.
    obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₅.mem :=
      d₄.frame.trans (f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩)
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
      rw [f₅.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dDS.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp only; omega) hi]
      exact d₄.data i hi
    show Spec.Sm4.blocksAt s₅.mem D n = _
    rw [blocksAt_of_dinv hd₅, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ D j

end VG.Proof.Sm4.X86_64
