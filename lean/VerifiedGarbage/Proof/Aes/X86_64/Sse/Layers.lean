module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.LinearX
public import VerifiedGarbage.Proof.Aes.X86_64.Encrypt
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the kernel's checks of the layers (`sbox_check`, `mixColumns_check`, …), which
-- a change to the proofs of the rounds or the groups need not run again.

/-!
# The layers of bitsliced AES in SSE2 registers, on x86-64

Each layer of `Impl/Aes/X86_64/Sse.lean` acts on each quadword of
`xmm0 … xmm7` as `Encrypt.lean`'s layer acts on the general-purpose
registers, and is checked the same way by the quadword-lane evaluator
(`StraightX`): the S-box on the truth tables of its 256 inputs, the linear
layers on the lane domain, against the same bits (`toBsG`, `srG`, …). The
statements are those of `Encrypt.lean`, for each quadword `l` (`QX s l`):
quadword 0 holds blocks 0–3, quadword 1 blocks 4–7.
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Spec.Aes (sbox)
open VG.Proof.Aes.X86_64 (inT inTs row_inTs)

/-- Quadword `l` of the state's words. -/
abbrev QX (s : State) (l i : Nat) : BitVec 64 := qword (s.xmm (q i)) l

/-! ## The S-box -/

def sboxCfg : Cfg := { base := .rcx, slots := spills }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((sboxT inTs).getD j 0)

theorem sbox_check : check (table 64 256) sboxCfg sboxCode sboxEnv sboxPost = true := by
  lit_decide

theorem sbox_writes : sboxCode.all (fun i => i.dst == none || i.dst == some .rax) = true := by
  lit_decide

/-- The S-box, at every bit position of each quadword of `q 0 … q 7`. It
writes `rax`, the spill slots, and no other general-purpose register. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ l < 2, ∀ j < 8, ∀ p < 64, (QX s' l j).getLsbD p = (sbox (bsByte (QX s l) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      (∀ x, (sboxCode.all fun i => xdst i != some x) = true → s'.xmm x = s.xmm x) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((sboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (fun l => TableRel p (bsByte (QX s l) p).toNat) sboxCfg e' s s'
        (fun r => (sboxCode.all fun i => xdst i != some r) = false)
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (fun l _ => table_sound hp (bsByte (QX s l) p).isLt) hok
      ⟨fun r a h l hl => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
        (fun _ _ h => by cases h)⟩ he
    have hc := (bsByte (QX s l) p).isLt
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_arith)
  have hw := List.all_eq_true.mp sbox_writes
  refine ⟨s', hs', fun l hl j hj p hp => ?_, p₀.rd, p₀.wr, p₀.cf, p₀.zf, fun r hr => p₀.gpr r ?_,
    fun x hx => p₀.other x (by simp [hx]), p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := Straight.run_unique hs'' hs'
    have hc := (bsByte (QX s l) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj) l hl
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp
  · intro h
    obtain ⟨i, hi, hd⟩ := List.all_eq_false.mp h
    have := hw i hi
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hd
    rw [hd] at this
    simp at this
    exact hr this

/-! ## The linear layers -/

/-- No memory. -/
def linCfg : Cfg := { base := .rcx, slots := 0 }

def qIns : List (XReg × Nat) := (List.range 8).map fun k => (q k, k)

def qOuts (g : Nat → Nat → List Nat) : List (XReg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-- ShiftRows' masks, loaded into `m 1` and `m 2`. -/
def srConsts : List (XReg × BitVec 64) := srMasks.map fun (k, v) => (m (1 + k), v)

theorem toBs_check : check (lanes 64 9) linCfg toBs (linEnv qIns) (linPost 9 (qOuts toBsG)) = true := by
  decide +kernel

theorem fromBs_check : check (lanes 64 9) linCfg fromBs (linEnv qIns) (linPost 9 (qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    check (lanes 64 9) linCfg srBody (linEnv qIns srConsts) (linPost 9 (qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    check (lanes 64 9) linCfg mixColumns (linEnv qIns) (linPost 9 (qOuts mcG)) = true := by
  decide +kernel

/-! ## On the machine -/

/-- What every layer keeps: all but `rax` of the general-purpose registers,
and memory. -/
structure Keeps (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₂.mem.trans h₁.mem⟩

theorem linCfg_ok (s : State) : Ok linCfg s := ⟨fun k hk => by simp [linCfg] at hk, by simp [linCfg]⟩

theorem frame_nil {b : Addr} {m m' : Mem} (h : Frame [⟨b, 0⟩] m m') : m' = m :=
  funext fun x => h x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [Region.Contains]

theorem gpr_keep {is : List Instr} (hw : is.all (fun i => i.dst == none || i.dst == some .rax) = true)
    {r : Reg} (hr : r ≠ .rax) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have := List.all_eq_true.mp hw i hi
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h <;> simp [h, Ne.symm hr]

theorem q_linear {is : List Instr} {g : Nat → Nat → List Nat} {cs : List (XReg × BitVec 64)}
    (hchk : check (lanes 64 9) linCfg is (linEnv qIns cs) (linPost 9 (qOuts g)) = true)
    (hw : is.all (fun i => i.dst == none || i.dst == some .rax) = true)
    {s : State} (hcs : ∀ r v, (r, v) ∈ cs → ∀ l < 2, qword (s.xmm r) l = v) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ l < 2, ∀ j < 8, ∀ p < 64, (QX s' l j).getLsbD p = xorBits (QX s l) (g j p)) ∧ Keeps s s' := by
  obtain ⟨s', hs', hout, hrd, hwr, -, -, hgpr, -, hfr⟩ := linear_ok hchk (linCfg_ok s) (QX s)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, fun _ _ => rfl⟩) hcs
  have hmem : ∀ j < 8, (q j, g j) ∈ qOuts g := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun l hl j hj p hp => hout (q j) (g j) (hmem j hj) l hl p hp,
    ⟨hrd, hwr, fun r hr => hgpr r (gpr_keep hw hr), frame_nil hfr⟩⟩

theorem toBs_ok (s : State) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ l < 2, ∀ j < 8, ∀ p < 64, (QX s' l j).getLsbD p =
        (QX s l (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) ∧ Keeps s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear (cs := []) toBs_check (by decide +kernel) (fun _ _ h => by cases h)
  refine ⟨s', hs', fun l hl j hj p hp => ?_, rest⟩
  rw [hout l hl j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega_arith)]

theorem fromBs_ok (s : State) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ l < 2, ∀ k < 8, ∀ t < 64, (QX s' l k).getLsbD t =
        (QX s l (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4)))) ∧ Keeps s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear (cs := []) fromBs_check (by decide +kernel) (fun _ _ h => by cases h)
  refine ⟨s', hs', fun l hl j hj p hp => ?_, rest⟩
  rw [hout l hl j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega_arith)]

theorem srBody_ok {s : State} (hm : ∀ k < 2, ∀ l < 2, qword (s.xmm (m (1 + k))) l = (srMasks.getD k (0, 0)).2) :
    ∃ s', runBlock isa srBody s = some s' ∧
      (∀ l < 2, ∀ j < 8, ∀ p < 64, (QX s' l j).getLsbD p = (QX s l j).getLsbD (srSrc p)) ∧ Keeps s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide +kernel) (fun r v h l hl => by
    simp only [srConsts, srMasks, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hm 0 (by decide) l hl
    · exact hm 1 (by decide) l hl)
  refine ⟨s', hs', fun l hl j hj p hp => ?_, rest⟩
  rw [hout l hl j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega_arith)]

theorem mixColumns_ok (s : State) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ l < 2, ∀ j < 8, ∀ p < 64, (QX s' l j).getLsbD p = termsXor (QX s l) (mcTerms j p)) ∧
      Keeps s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear (cs := []) mixColumns_check (by decide +kernel)
    (fun _ _ h => by cases h)
  refine ⟨s', hs', fun l hl j hj p hp => ?_, rest⟩
  rw [hout l hl j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

end VG.Proof.Aes.X86_64.Sse
