module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Proof.Aes.Sbox0
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.LinearX

/-! # The layers of bitsliced AES in SSE2, by evaluation -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-- The slots of the scratch buffer the layers use. -/
def cfg : Cfg := { base := .r9, slots := 18 }

def ins (r : Nat → XReg) : List (XReg × Nat) := (List.range 8).map fun j => (r j, j)

def outs (r : Nat → XReg) (g : Nat → Nat → List Nat) : List (XReg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (r j, g j)

/-- The masks, in their slots. -/
def maskVals : List (Nat × BitVec 64) :=
  ((List.range 6).map fun i => (maskSlot i, idxMask i)) ++
    [(sr2Slot, sr2Mask), (highSlot, highMask), (oddSlot, oddMask)]

/-- Input words in registers, and the masks in their slots. -/
def env (r : Nat → XReg) : Env (Nat × Nat) :=
  { reg := fun x => ((ins r).find? (·.1 == x)).map fun i => inWord i.2
    slot := fun k => (maskVals.find? (·.1 == k)).map fun m => (m.2.toNat, 0) }

def keepsMasks (e : Env (Nat × Nat)) : Bool :=
  maskVals.all fun m => e.slot m.1 == some (m.2.toNat, 0)

def post (r : Nat → XReg) (g : Nat → Nat → List Nat) (e : Env (Nat × Nat)) : Bool :=
  linPost 9 (outs r g) e && keepsMasks e

/-- Pairs as bit numbers. -/
def atoms (T : Nat → Nat → List (Nat × Nat)) (j p : Nat) : List Nat := (T j p).map fun t => 64 * t.1 + t.2

/-- `toBs`: from words `k + 4 c`, half `c` (columns `2 c`, `2 c + 1`) of block `k`. -/
def toBsT (j p : Nat) : List (Nat × Nat) :=
  [(p % 4 + 4 * (byteAt 4 false p / 8), 8 * (byteAt 4 false p % 8) + j)]

/-- `fromBs`: to those words. -/
def fromBsT (w t : Nat) : List (Nat × Nat) := [(t % 8, posAt 4 false (8 * (w / 4) + t / 8) (w % 4))]

theorem toBs_check : check (lanes 64 9) cfg toBs (env q) (post q (atoms toBsT)) = true := by decide +kernel
theorem fromBs_check : check (lanes 64 9) cfg fromBs (env q) (post q (atoms fromBsT)) = true := by decide +kernel
theorem mc0_check : check (lanes 64 9) cfg (mixColumns false) (env p)
    (post q (atoms (mixT mcCoeffs 4 false))) = true := by decide +kernel
theorem mc1_check : check (lanes 64 9) cfg (mixColumns true) (env p)
    (post q (atoms (mixT mcCoeffs 4 true))) = true := by decide +kernel
theorem sr2p_check : check (lanes 64 9) cfg (sr2 p .xmm0 .xmm1) (env p) (post p (atoms (sr2T 4))) = true := by
  decide +kernel
theorem sr2q_check : check (lanes 64 9) cfg (sr2 q .xmm8 .xmm9) (env q) (post q (atoms (sr2T 4))) = true := by
  decide +kernel

theorem invMc0_check : check (lanes 64 9) cfg (invMixColumns false) (env p)
    (post q (atoms (mixT invMcCoeffs 4 false))) = true := by decide +kernel
theorem invMc1_check : check (lanes 64 9) cfg (invMixColumns true) (env p)
    (post q (atoms (mixT invMcCoeffs 4 true))) = true := by decide +kernel

/-- A round key's bits between `keyMid` and `keyOut`: `h` of the slice's number, in form `f`. -/
def midT (f : Bool) (h p : Nat) : List (Nat × Nat) :=
  [(4 * (byteAt 4 f p / 8), 8 * (byteAt 4 f p % 8) + (4 * h + p % 4))]

def keyMidT (j p : Nat) : List (Nat × Nat) :=
  if j % 4 = 0 then midT false (j / 4) p else if j % 4 = 1 then midT true (j / 4) p else [(j, p)]
theorem keyMid_check : check (lanes 64 9) cfg keyMid (env q) (post q (atoms keyMidT)) = true := by decide +kernel

def keyOutT (j p : Nat) : List (Nat × Nat) := [(4 * (j / 4), p - p % 4 + j % 4)]
theorem keyOut_check : check (lanes 64 9) cfg keyOut (env q) (post q (atoms keyOutT)) = true := by decide +kernel

/-- `moveBack`: slices as they are. -/
def idT (j p : Nat) : List (Nat × Nat) := [(j, p)]
theorem move_check : check (lanes 64 9) cfg moveBack (env p) (post q (atoms idT)) = true := by decide +kernel

/-- The slots the S-boxes spill to. -/
def spillCfg : Cfg := { base := .r9, slots := 9 }

def sEnv : Env Nat :=
  { reg := fun x => ((ins q).find? (·.1 == x)).map fun i => sbIn i.2
    slot := fun _ => none }
def sPost (T : List Nat) (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (p j) == some (T.getD j 0)
theorem sbox_check : check (table 64 256) spillCfg subBytes sEnv (sPost sbox0T) = true := by decide +kernel
theorem invSbox_check : check (table 64 256) spillCfg invSubBytes sEnv (sPost invSbox0T) = true := by decide +kernel

/-! ## The machine -/

/-- The slices in the registers `r j`, in quadword `l`. -/
def lane (r : Nat → XReg) (s : State) (l : Nat) : Nat → BitVec 64 := fun j => qword (s.xmm (r j)) l

/-- The registers `r j` hold the eight states, in form `f`. -/
def Holds (f : Bool) (r : Nat → XReg) (s : State) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ l < 2, BsRel 4 f (lane r s l) fun k => S (4 * l + k)

/-- The spills and masks may be written, and the masks are there. -/
structure Env0 (s : State) : Prop where
  ok : Ok cfg s
  masks : ∀ m ∈ maskVals, ∀ l < 2, qword (s.mem.readW (xAddr (s.gpr .r9) m.1) 128) l = m.2

/-- What a layer keeps. -/
structure Keep (s s' : State) : Prop where
  env : Env0 s'
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotRegion cfg s] s.mem s'.mem

theorem Keep.trans {s s' s'' : State} (h : Keep s s') (h' : Keep s' s'') : Keep s s'' where
  env := h'.env
  gpr := h'.gpr.trans h.gpr
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  frame := h.frame.trans (by
    have := h'.frame
    rwa [slotRegion, h.gpr] at this)

theorem mask_slots : ∀ m ∈ maskVals, m.1 < 18 := by decide

theorem rel_env {r : Nat → XReg} {s : State} (he : Env0 s) :
    Rel (fun l => LaneRel 9 (assign (lane r s l) (2 ^ 9))) cfg (env r) s := by
  refine ⟨fun x a h l hl => ?_, fun k a hk h l hl => ?_, (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  · simp only [env, Option.map_eq_some_iff] at h
    obtain ⟨⟨x', i⟩, hf, rfl⟩ := h
    have hx : x' = x := by simpa using List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [ins, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨j, hj, rfl, rfl⟩ := hm
    rw [← hx]
    exact inWord_rel (lane r s l) (by omega)
  · simp only [env, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', v⟩, hf, rfl⟩ := h
    have hx : k' = k := by simpa using List.find?_some hf
    subst hx
    rw [show s.gpr cfg.base = s.gpr .r9 from rfl, he.masks _ (List.mem_of_find?_eq_some hf) l hl]
    exact lanes_sound.const rfl

/-- A linear layer that the evaluator accepts. -/
theorem layer_ok {is : List Instr} {r r' : Nat → XReg} {T : Nat → Nat → List (Nat × Nat)}
    (hchk : check (lanes 64 9) cfg is (env r) (post r' (atoms T)) = true)
    (hT : ∀ j < 8, ∀ p < 64, ∀ t ∈ T j p, t.2 < 64) (hdst : (is.all fun i => i.dst == none) = true)
    {s : State} (he : Env0 s) :
    ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧
      ∀ l < 2, ∀ j < 8, ∀ p < 64, (lane r' s' l j).getLsbD p = termsXor (lane r s l) (T j p) := by
  obtain ⟨e', hev, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', P⟩ := run (fun _ _ => lanes_sound) he.ok (rel_env he) hev
  simp only [post, Bool.and_eq_true] at hpost
  have hg : s'.gpr = s.gpr := funext fun x => P.gpr x fun h => by
    obtain ⟨i, hi, h⟩ : ∃ i ∈ is, ¬ i.dst ≠ some x := by
      simpa using h
    have := List.all_eq_true.mp hdst i hi
    simp_all
  refine ⟨s', hs', ⟨⟨P.ok, fun m hm l hl => ?_⟩, hg, P.rd, P.wr, P.frame⟩, fun l hl j hj q hq => ?_⟩
  · have h1 := List.all_eq_true.mp hpost.2 m hm
    simp only [beq_iff_eq] at h1
    have h2 := P.rel.slot m.1 _ (mask_slots m hm) h1 l hl
    have h3 : LaneRel 9 (assign (lane r s l) (2 ^ 9)) (m.2.toNat, 0) m.2 := lanes_sound.const rfl
    exact BitVec.eq_of_getLsbD_eq fun b hb => (h2.2 b hb).trans (h3.2 b hb).symm
  · obtain ⟨h1, h2⟩ := outOk_spec (List.all_eq_true.mp hpost.1 (r' j, atoms T j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    have := outWord_rel_of_lt h2 (P.rel.reg (r' j) _ h1 l hl) q hq
    rw [show lane r' s' l j = qword (s'.xmm (r' j)) l from rfl, this]
    exact xorBits_map (lane r s l) (T j q) (hT j hj q hq)

theorem mask_ge : ∀ m ∈ maskVals, 9 ≤ m.1 := by decide

/-- An S-box that the evaluator accepts, `g` its table's function. -/
theorem sub_ok {is : List Instr} {T : List Nat} {g : Byte → Byte}
    (hchk : check (table 64 256) spillCfg is sEnv (sPost T) = true)
    (hT : ∀ c j, c < 256 → j < 8 → (T.getD j 0).testBit c = (g (BitVec.ofNat 8 c)).getLsbD j)
    (hdst : (is.all fun i => i.dst == none) = true) {s : State} (he : Env0 s) :
    ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧
      ∀ l < 2, ∀ j < 8, ∀ x < 64, (lane p s' l j).getLsbD x = (g (bsByte (lane q s l) x)).getLsbD j := by
  obtain ⟨e', hev, hpost⟩ := of_check _ _ hchk
  have hok : Ok spillCfg s := ⟨fun k hk => he.ok.slotIn k (Nat.lt_of_lt_of_le hk (by decide)), by decide⟩
  have key : ∀ x < 64, ∃ s', runBlock isa is s = some s' ∧
      Post (fun l => TableRel x (bsByte (lane q s l) x).toNat) spillCfg e' s s'
        (fun r => (is.all fun i => xdst i != some r) = false) (fun r => (is.all fun i => i.dst != some r) = false) := by
    intro x hx
    refine run (fun l _ => table_sound hx (bsByte (lane q s l) x).isLt) hok ⟨fun r a h l hl => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩ hev
    simp only [sEnv, Option.map_eq_some_iff] at h
    obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
    have hr : r' = r := by simpa using List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [ins, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨j, hj, rfl, rfl⟩ := hm
    rw [← hr]
    simp only [TableRel, sbIn, testBit_tableOf, (bsByte (lane q s l) x).isLt, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hj]
    rfl
  obtain ⟨s', hs', P⟩ := key 0 (by decide)
  have hg : s'.gpr = s.gpr := funext fun x => P.gpr x fun h => by
    obtain ⟨i, hi, h⟩ : ∃ i ∈ is, ¬ i.dst ≠ some x := by simpa using h
    have := List.all_eq_true.mp hdst i hi
    simp_all
  have hfr : Frame [⟨s.gpr .r9, 144⟩] s.mem s'.mem := P.frame
  refine ⟨s', hs', ⟨⟨he.ok.congr (by rw [hg]) P.wr, fun m hm l hl => ?_⟩, hg, P.rd, P.wr,
    hfr.sub fun r hr => ?_⟩, fun l hl j hj x hx => ?_⟩
  · rw [hg, hfr.readW (r := ⟨xAddr (s.gpr .r9) m.1, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact he.masks m hm l hl
    · rw [List.mem_singleton.mp hr]
      have := mask_ge m hm
      have := mask_slots m hm
      exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [List.mem_singleton.mp hr]
    refine ⟨_, List.mem_singleton.mpr rfl, fun x h => ?_⟩
    simp only [Region.Contains, slotRegion, cfg] at h ⊢
    omega
  · obtain ⟨s'', hs'', P'⟩ := key x hx
    obtain rfl : s'' = s' := Option.some.inj (hs''.symm.trans hs')
    have h1 := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h1
    have h2 := P'.rel.reg (p j) _ h1 l hl
    simp only [TableRel] at h2
    show (qword (s''.xmm (p j)) l).getLsbD x = _
    rw [← h2, hT _ j (bsByte (lane q s l) x).isLt hj]
    simp

end VG.Proof.Aes.X86_64.Sse
