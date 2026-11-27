module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.X86_64.LinearX
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Aes.Memory
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The bitsliced engine of AES on x86-64

The layers by evaluation, the rounds, a batch of eight blocks, the key setup,
and copying blocks in and out of the batch's buffer.
-/

@[expose] public section

section

/-! # The layers of bitsliced AES in SSE2, by evaluation -/

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

/-- `post`, with the lanes of the outputs' words given as numbers. -/
def postS (r : Nat → XReg) (S : Nat → Nat) (e : Env (Nat × Nat)) : Bool :=
  ((List.range 8).all fun j => outOkS 64 9 (e.reg (r j)) (S j)) && keepsMasks e

theorem check_of {is : List Instr} {e : Env (Nat × Nat)} {r : Nat → XReg} {T : Nat → Nat → List (Nat × Nat)}
    {S : Nat → Nat} (hS : ∀ j, mk 64 (atoms T j) 64 = S j)
    (h : check (lanes 64 9) cfg is e (postS r S) = true) : check (lanes 64 9) cfg is e (post r (atoms T)) = true := by
  obtain ⟨e', he, hp⟩ := of_check _ _ h
  rw [postS, Bool.and_eq_true] at hp
  rw [check, he]
  show (linPost 9 (outs r (atoms T)) e' && keepsMasks e') = true
  rw [hp.2, Bool.and_true]
  refine List.all_eq_true.mpr fun o ho => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
  exact outOkW_of (hS j) (List.all_eq_true.mp hp.1 j hj)

theorem toBs_check : check (lanes 64 9) cfg toBs (env q) (post q (atoms toBsT)) = true := by decide +kernel
theorem fromBs_check : check (lanes 64 9) cfg fromBs (env q) (post q (atoms fromBsT)) = true := by decide +kernel
theorem mc0_check : check (lanes 64 9) cfg (mixColumns false) (env p)
    (post q (atoms (mixT mcCoeffs 4 false))) = true := check_of (mixTS_eq 64 mcCoeffs 4 false) (by decide +kernel)
theorem mc1_check : check (lanes 64 9) cfg (mixColumns true) (env p)
    (post q (atoms (mixT mcCoeffs 4 true))) = true := check_of (mixTS_eq 64 mcCoeffs 4 true) (by decide +kernel)
theorem sr2p_check : check (lanes 64 9) cfg (sr2 p .xmm0 .xmm1) (env p) (post p (atoms (sr2T 4))) = true := by
  decide +kernel
theorem sr2q_check : check (lanes 64 9) cfg (sr2 q .xmm8 .xmm9) (env q) (post q (atoms (sr2T 4))) = true := by
  decide +kernel

theorem invMc0_check : check (lanes 64 9) cfg (invMixColumns false) (env p)
    (post q (atoms (mixT invMcCoeffs 4 false))) = true := check_of (mixTS_eq 64 invMcCoeffs 4 false) (by decide +kernel)
theorem invMc1_check : check (lanes 64 9) cfg (invMixColumns true) (env p)
    (post q (atoms (mixT invMcCoeffs 4 true))) = true := check_of (mixTS_eq 64 invMcCoeffs 4 true) (by decide +kernel)

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

end

section

/-! # The rounds of bitsliced AES in SSE2 -/

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-! ## Quadwords -/

theorem qword_readW (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    qword (m.readW a 128) l = m.readW (a + BitVec.ofNat 64 (8 * l)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((64 * l + i) / 8) = a + BitVec.ofNat 64 (8 * l) + BitVec.ofNat 64 (i / 8) by
    rw [show (64 * l + i) / 8 = 8 * l + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)

theorem dup44 (a : BitVec 128) : shufDwords a 0x44 = ofDwords (dword a 0) (dword a 1) (dword a 0) (dword a 1) := rfl
theorem dupee (a : BitVec 128) : shufDwords a 0xee = ofDwords (dword a 2) (dword a 3) (dword a 2) (dword a 3) := rfl

theorem qword_dup44 (a : BitVec 128) {l : Nat} (hl : l < 2) : qword (shufDwords a 0x44) l = qword a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_qword _ hi, getLsbD_qword _ hi, dup44, getLsbD_ofDwords]
  simp only [getLsbD_dword]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  all_goals
    rcases (by omega : i < 32 ∨ 32 ≤ i) with h | h
    all_goals
      simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right, decide_eq_true, Bool.true_and]
      exact congrArg _ (by omega)

theorem qword_dupee (a : BitVec 128) {l : Nat} (hl : l < 2) : qword (shufDwords a 0xee) l = qword a 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_qword _ hi, getLsbD_qword _ hi, dupee, getLsbD_ofDwords]
  simp only [getLsbD_dword]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  all_goals
    rcases (by omega : i < 32 ∨ 32 ≤ i) with h | h
    all_goals
      simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right, decide_eq_true, Bool.true_and]
      exact congrArg _ (by omega)

theorem qword_unpckl (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    qword (XBinOp.eval .punpcklqdq a b) l = if l = 0 then qword a 0 else qword b 0 := by
  simp only [XBinOp.eval]; rw [StraightY.qword_app _ _ hl]

theorem qword_unpckh (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    qword (XBinOp.eval .punpckhqdq a b) l = if l = 0 then qword a 1 else qword b 1 := by
  simp only [XBinOp.eval]; rw [StraightY.qword_app _ _ hl]

/-! ## Adding a round key -/

/-- The round key `rk` is at `a`, in slices in form `f`, a quadword for each. -/
def KeyAt (m : Mem) (a : Addr) (f : Bool) (rk : List Byte) : Prop :=
  BsRel 4 f (fun j => m.readW (a + BitVec.ofNat 64 (8 * j)) 64) fun _ => rkState rk

/-- One step of `addRoundKey`. -/
theorem arkStep (r0 r1 t u : XReg) (i : Nat) (s : State)
    (h : r0 ≠ t ∧ r0 ≠ u ∧ r1 ≠ t ∧ r1 ≠ u ∧ t ≠ u ∧ r0 ≠ r1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px r0 u, px r1 t] s = some s' ∧
      (∀ l < 2, qword (s'.xmm r0) l = qword (s.xmm r0) l ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i)) 64) ∧
      (∀ l < 2, qword (s'.xmm r1) l = qword (s.xmm r1) l ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i + 8)) 64) ∧
      (∀ x, x ≠ r0 → x ≠ r1 → x ≠ t → x ≠ u → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hea : s.ea (Impl.Aes.X86_64.at_ kp (16 * i)) = s.gpr kp + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, Impl.Aes.X86_64.at_, BitVec.ofInt_natCast]
  have hrun : runBlock isa [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px r0 u, px r1 t] s =
      some ((XOp.bin XBinOp.pxor r1 t).exec ((XOp.bin XBinOp.pxor r0 u).exec ((XOp.pshufd t t 0xee).exec
        ((XOp.pshufd u t 0x44).exec (s.setXmm t (s.mem.readW (s.gpr kp + BitVec.ofNat 64 (16 * i)) 128)))))) := by
    simp only [dupLow, dupHigh, px, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128, hea,
      hin, ite_true, Option.map_some]
  refine ⟨_, hrun, ?_, ?_, ?_, by simp only [XOp.exec, gpr_setXmm], by simp only [XOp.exec, mem_setXmm],
    by simp only [XOp.exec, rd_setXmm], by simp only [XOp.exec, wr_setXmm]⟩
  · intro l hl
    simp only [XOp.exec, xmm_setXmm, h1, h2, h3, h4, h5, h6, h1.symm, h5.symm, h6.symm,
      ite_true, ite_false, XBinOp.eval, StraightY.qword_xor, qword_dup44 _ hl]
    rw [qword_readW _ _ (by decide)]; simp
  · intro l hl
    simp only [XOp.exec, xmm_setXmm, h1, h2, h3, h4, h5, h1.symm, h5.symm, h6.symm,
      ite_true, ite_false, XBinOp.eval, StraightY.qword_xor, qword_dupee _ hl]
    rw [qword_readW _ _ (by decide), BitVec.add_assoc, ← BitVec.ofNat_add]
  · intro x a b c d
    simp only [XOp.exec, xmm_setXmm, a, b, c, d, ite_false]

/-- The registers of the slices, and two others, as `addRoundKey` takes them. -/
def Regs (r : Nat → XReg) (t u : XReg) : Prop := (∀ j < 8, r j ≠ t ∧ r j ≠ u) ∧ t ≠ u ∧ ∀ i < 8, ∀ j < 8, r i = r j → i = j

theorem regs_q : Regs q .xmm8 .xmm9 := ⟨by decide, by decide, by decide⟩
theorem regs_p : Regs p .xmm0 .xmm1 := ⟨by decide, by decide, by decide⟩

theorem ark_steps {r : Nat → XReg} {t u : XReg} (hr : Regs r t u) (s : State)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun i =>
        [.movdquLoad t (Impl.Aes.X86_64.at_ kp (16 * i)), dupLow u t, dupHigh t t, px (r (2 * i)) u, px (r (2 * i + 1)) t]) s = some s' ∧
      (∀ l < 2, ∀ j < 8, lane r s' l j = if j < 2 * n then lane r s l j ^^^ s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64
        else lane r s l j) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j _ => by simp, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := ih (by omega)
    obtain ⟨ht, htu, hinj⟩ := hr
    obtain ⟨s2, e2, ha, hb, hc, g2, m2, r2, w2⟩ := arkStep (r (2 * n)) (r (2 * n + 1)) t u n s1
      ⟨(ht _ (by omega)).1, (ht _ (by omega)).2, (ht _ (by omega)).1, (ht _ (by omega)).2, htu,
        fun h => by have := hinj _ (by omega) _ (by omega) h; omega⟩
      (by rw [r1, w1, g1]; exact hin n (by omega))
    refine ⟨s2, ?_, fun l hl j hj => ?_, g2.trans g1, m2.trans m1, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, VG.Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · rw [g1, m1] at ha hb
      by_cases h0 : j = 2 * n
      · subst h0
        have := h1 l hl (2 * n) hj
        simp only [Nat.lt_irrefl, ite_false] at this
        simp only [lane] at this ⊢
        rw [ha l hl, this, show 16 * n = 8 * (2 * n) by omega]; simp
      by_cases h0' : j = 2 * n + 1
      · subst h0'
        have := h1 l hl (2 * n + 1) hj
        simp only [show ¬ 2 * n + 1 < 2 * n by omega, ite_false] at this
        simp only [lane] at this ⊢
        rw [hb l hl, this, show 16 * n + 8 = 8 * (2 * n + 1) by omega]; simp; omega
      · have := h1 l hl j hj
        simp only [lane] at this ⊢
        rw [hc (r j) (fun h => h0 (hinj _ hj _ (by omega) h)) (fun h => h0' (hinj _ hj _ (by omega) h)) (ht j hj).1
          (ht j hj).2, this]
        simp only [show (j < 2 * (n + 1)) = (j < 2 * n) by apply propext; omega]

theorem keep_of {s s' : State} (he : Env0 s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : Keep s s' where
  env := ⟨he.ok.congr (by rw [hg]) hw, fun m h l hl => by rw [hm, hg]; exact he.masks m h l hl⟩
  gpr := hg
  rd := hr
  wr := hw
  frame := by rw [hm]; exact Frame.refl _ _

theorem ark_ok {r : Nat → XReg} {t u : XReg} (hr : Regs r t u) {s : State} (he : Env0 s)
    {f : Bool} {S : Nat → Spec.Aes.State} (hS : Holds f r s S) {rk : List Byte} (hK : KeyAt s.mem (s.gpr kp) f rk)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa (addRoundKey r t u) s = some s' ∧ Keep s s' ∧
      Holds f r s' fun k => Spec.Aes.addRoundKey (S k) rk := by
  obtain ⟨s', e, h, g, m, hrd, hwr⟩ := ark_steps hr s hin 4 (by decide)
  refine ⟨s', e, keep_of he g m hrd hwr, fun l hl => ?_⟩
  refine BsRel.addRoundKey (rk := fun _ => rk) (hS l hl) hK fun j hj x _ => ?_
  rw [h l hl j hj, ite_eq_left_of_eq_true _ _ (by simp; omega), BitVec.getLsbD_xor]

/-! ## The layers, on states -/

theorem sub_holds {f : Bool} {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f q s S) :
    ∃ s', runBlock isa subBytes s = some s' ∧ Keep s s' ∧ Holds f p s' fun k => (S k).map sbox0 := by
  obtain ⟨s', e, k, h⟩ := sub_ok sbox_check (fun _ _ => sbox0T_bit) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).map sbox0 fun j hj x hx => h l hl j hj x hx⟩

theorem invSub_holds {f : Bool} {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f q s S) :
    ∃ s', runBlock isa invSubBytes s = some s' ∧ Keep s s' ∧ Holds f p s' fun k => (S k).map invSbox0 := by
  obtain ⟨s', e, k, h⟩ := sub_ok invSbox_check (fun _ _ => invSbox0T_bit) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).map invSbox0 fun j hj x hx => h l hl j hj x hx⟩

theorem mc_holds (f : Bool) {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f p s S) :
    ∃ s', runBlock isa (Impl.Aes.X86_64.Sse.mixColumns f) s = some s' ∧ Keep s s' ∧
      Holds f q s' fun k => Spec.Aes.mixColumns (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok (is := Impl.Aes.X86_64.Sse.mixColumns f) (r := p) (r' := q)
    (T := mixT mcCoeffs 4 f) (by cases f; exact mc0_check; exact mc1_check)
    (fun j _ p hp => mixT_lt mcCoeffs f j (by decide) hp)
    (by cases f <;> decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).mixColumns fun j hj x hx => h l hl j hj x hx⟩

theorem invMc_holds (f : Bool) {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds f p s S) :
    ∃ s', runBlock isa (Impl.Aes.X86_64.Sse.invMixColumns f) s = some s' ∧ Keep s s' ∧
      Holds f q s' fun k => Spec.Aes.invMixColumns (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok (is := Impl.Aes.X86_64.Sse.invMixColumns f) (r := p) (r' := q)
    (T := mixT invMcCoeffs 4 f) (by cases f; exact invMc0_check; exact invMc1_check)
    (fun j _ p hp => mixT_lt invMcCoeffs f j (by decide) hp) (by cases f <;> decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).invMixColumns fun j hj x hx => h l hl j hj x hx⟩

theorem sr2_holds {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds true p s S) :
    ∃ s', runBlock isa (sr2 p .xmm0 .xmm1) s = some s' ∧ Keep s s' ∧
      Holds false p s' fun k => Spec.Aes.shiftRows (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok sr2p_check (by decide +kernel) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).sr2 fun j hj x hx => h l hl j hj x hx⟩

theorem invSr2_holds {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds false q s S) :
    ∃ s', runBlock isa (sr2 q .xmm8 .xmm9) s = some s' ∧ Keep s s' ∧
      Holds true q s' fun k => Spec.Aes.invShiftRows (S k) := by
  obtain ⟨s', e, k, h⟩ := layer_ok sr2q_check (by decide +kernel) (by decide) he
  exact ⟨s', e, k, fun l hl => (hS l hl).invSr2 fun j hj x hx => h l hl j hj x hx⟩

/-! ## Rounds -/

/-- Round key `i` as stored: `{63}` is added to all but the first. -/
def kr (w : List Byte) (i : Nat) : List Byte :=
  if i = 0 then Spec.Aes.roundKey w 0 else rk63 (Spec.Aes.roundKey w i)

/-- A middle round of the cipher. -/
def rnd (w : List Byte) (i : Nat) (s : Spec.Aes.State) : Spec.Aes.State :=
  Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (Spec.Aes.subBytes s))) (Spec.Aes.roundKey w i)

/-- The address of round key `i`. -/
def keyAddr (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (keysOff + 64 * i)

/-- The scratch buffer at `b`, with the round keys: what a batch needs. -/
structure Ready (b : Addr) (nr : Nat) (w : List Byte) (m : Mem) (rd wr : List Region) : Prop where
  sc : ⟨b, 2048⟩ ∈ wr ∨ ⟨b, 1480⟩ ∈ wr
  keys : ∀ i ≤ nr, KeyAt m (keyAddr b i) (i % 2 == 1) (kr w i)
  masks : ∀ k ∈ maskVals, ∀ l < 2, qword (m.readW (xAddr b k.1) 128) l = k.2
  nrs : nr = 10 ∨ nr = 12 ∨ nr = 14
  len : ∀ i ≤ nr, (Spec.Aes.roundKey w i).length = 16

variable {b : Addr} {nr : Nat} {w : List Byte}

theorem Ready.inWr {m : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {d n : Nat} (hd : d + n ≤ 1480) :
    InRegions wr (b + BitVec.ofNat 64 d) n := by
  rcases h.sc with h | h
  · exact ⟨_, h, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨_, h, Offset.contains_base _ hd (by omega)⟩

theorem Ready.frame {m m' : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {rs : List Region}
    (hf : Frame rs m m')
    (hk : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 keysOff, 960⟩ r ∧ Region.Disjoint ⟨b + BitVec.ofNat 64 144, 144⟩ r) :
    Ready b nr w m' rd wr where
  sc := h.sc
  nrs := h.nrs
  len := h.len
  keys i hi := by
    refine (h.keys i hi).congrW fun j hj => ?_
    have := h.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (fun r hr => (hk r hr).1) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  masks k hm l hl := by
    have h1 := mask_ge k hm
    have h2 := mask_slots k hm
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 144, 144⟩) ?_ (fun r hr => (hk r hr).2) (by decide)]
    · exact h.masks k hm l hl
    · exact Offset.contains _ (by omega) (by omega) (by decide)

/-- The state between layers: slices of `S` in form `f` in `r`, the next
round key `i` at `kp`; `s₁` is where the batch started. -/
structure RS (s₁ : State) (b : Addr) (nr : Nat) (w : List Byte) (cnt : BitVec 64) (i : Nat) (f : Bool) (r : Nat → XReg)
    (S : Nat → Spec.Aes.State) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  r9 : s.gpr .r9 = b
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → s.gpr x = s₁.gpr x
  cnt : s.gpr .r10 = cnt
  kpAt : s.gpr .rax = keyAddr b i
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨b, 288⟩] s₁.mem s.mem
  holds : Holds f r s S

theorem RS.env {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f : Bool} {r : Nat → XReg} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt i f r S s) : Env0 s where
  ok := ⟨fun k hk => by
    rw [show s.gpr cfg.base = b from h.r9]
    exact h.ready.inWr (by simp only [cfg] at hk; omega), by decide⟩
  masks := by rw [h.r9]; exact h.ready.masks

theorem low_disj (b : Addr) : ∀ r ∈ [(⟨b, 288⟩ : Region)],
    Region.Disjoint ⟨b + BitVec.ofNat 64 keysOff, 960⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by decide) (by decide)

theorem RS.keep {s₁ s s' : State} {cnt : BitVec 64} {i : Nat} {f f' : Bool} {r r' : Nat → XReg}
    {S S' : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i f r S s) (k : Keep s s') (hh : Holds f' r' s' S') :
    RS s₁ b nr w cnt i f' r' S' s' := by
  have hf : Frame [⟨b, 288⟩] s.mem s'.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine ⟨⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩, by rw [k.gpr, h.r9],
    fun x a c => by rw [k.gpr, h.gpr x a c], by rw [k.gpr, h.cnt], by rw [k.gpr, h.kpAt], k.rd.trans h.rd,
    k.wr.trans h.wr, h.frame.trans hf, hh⟩
  · refine (h.ready.keys i hi).congrW fun j hj => ?_
    have := h.ready.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  · have := k.env.masks
    rwa [k.gpr, h.r9] at this

theorem RS.step {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f f' : Bool} {r r' : Nat → XReg}
    {S S' : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i f r S s) {is : List Instr}
    (hs : ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧ Holds f' r' s' S') :
    WP isa (.block is) s (RS s₁ b nr w cnt i f' r' S') := by
  obtain ⟨s', e, k, hh⟩ := hs
  exact WP.of_runBlock ⟨s', e, h.keep k hh⟩

theorem RS.congr {s₁ s : State} {cnt : BitVec 64} {i : Nat} {f : Bool} {r : Nat → XReg}
    {S S' : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i f r S s) (hS : ∀ k < 8, S k = S' k) :
    RS s₁ b nr w cnt i f r S' s :=
  { h with holds := fun l hl => (h.holds l hl).congr fun k hk => hS _ (by omega) }

theorem RS.skip {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i false r S s) :
    RS s₁ b nr w cnt i true r (fun k => Spec.Aes.shiftRows (S k)) s :=
  { h with holds := fun l hl => (h.holds l hl).skipShift }

theorem RS.skipInv {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} (h : RS s₁ b nr w cnt i true r S s) :
    RS s₁ b nr w cnt i false r (fun k => Spec.Aes.invShiftRows (S k)) s :=
  { h with holds := fun l hl => (h.holds l hl).skipInvShift }

theorem RS.ark {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg} {t u : XReg} (hr : Regs r t u)
    {S : Nat → Spec.Aes.State} {f : Bool} (hf : f = (i % 2 == 1)) (hi : i ≤ nr) (h : RS s₁ b nr w cnt i f r S s) :
    WP isa (.block (Impl.Aes.X86_64.Sse.addRoundKey r t u)) s
      (RS s₁ b nr w cnt i f r fun k => Spec.Aes.addRoundKey (S k) (kr w i)) := by
  subst hf
  refine h.step (ark_ok hr h.env h.holds (by rw [show s.gpr kp = keyAddr b i from h.kpAt]; exact h.ready.keys i hi)
    fun j hj => ?_)
  rw [show s.gpr kp = keyAddr b i from h.kpAt, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  have := h.ready.nrs
  obtain ⟨R, hR, hc⟩ := h.ready.inWr (d := keysOff + 64 * i + 16 * j) (n := 16) (by simp only [keysOff]; omega)
  exact ⟨R, List.mem_append_right _ hR, hc⟩

theorem RS.next {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} {f : Bool} (h : RS s₁ b nr w cnt i f r S s) :
    WP isa (.block [nextKey]) s (RS s₁ b nr w cnt (i + 1) f r S) := by
  apply WP.of_runBlock
  have e : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  simp only [nextKey, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, e, Option.bind_some,
    Option.some.injEq, exists_eq_left', show Impl.Aes.X86_64.Sse.kp = Reg.rax from rfl]
  refine ⟨h.ready, ?_, fun x a c => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.r9
  · rw [gpr_setReg_of_ne _ _ a, gpr_arithFlags]; exact h.gpr x a c
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.cnt
  · rw [gpr_setReg_self, h.kpAt, keyAddr, keyAddr, BitVec.add_assoc]
    congr 1
    rw [show keysOff + 64 * (i + 1) = keysOff + 64 * i + 64 by omega, BitVec.ofNat_add (keysOff + 64 * i)]
    rfl

theorem roundA_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 1) (hn : i ≤ nr)
    (h : RS s₁ b nr w cnt i false q S s) :
    WP isa (.block roundA) s (RS s₁ b nr w cnt (i + 1) true q fun k => rnd w i (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h.step (sub_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.skip.step (mc_holds true h2.env h2.skip.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_q (by simp [hi]) hn) fun s4 h4 => ?_
  refine WP.mono h4.next fun s5 h5 => h5.congr fun k _ => ?_
  rw [kr, ite_eq_right (by omega), round63 _ (h.ready.len i hn), rnd]

theorem roundB_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 0) (h0 : i ≠ 0)
    (hn : i ≤ nr) (h : RS s₁ b nr w cnt i true q S s) :
    WP isa (.block roundB) s (RS s₁ b nr w cnt (i + 1) false q fun k => rnd w i (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (h.step (sub_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.step (sr2_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.step (mc_holds false h3.env h3.holds)) fun s4 h4 => ?_
  refine WP.mono (h4.ark regs_q (by simp [hi]) hn) fun s5 h5 => ?_
  refine WP.mono h5.next fun s6 h6 => h6.congr fun k _ => ?_
  rw [kr, ite_eq_right h0, round63 _ (h.ready.len i hn), rnd]

end VG.Proof.Aes.X86_64.Sse

end

section

/-! # A batch of eight blocks -/

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-- Block `i` of the buffer. -/
def bufAddr (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (16 * bufSlot i)

/-- The buffer holds the eight blocks `S`. -/
def BufIs (m : Mem) (b : Addr) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 8, ∀ n < 16, m (bufAddr b i + BitVec.ofNat 64 n) = (S i).getD n 0

theorem ea_slot (s : State) (k : Nat) : s.ea (slot k) = s.gpr .r9 + BitVec.ofNat 64 (16 * k) := by
  simp only [State.ea, slot, BitVec.ofInt_natCast]

/-! ## Loading the buffer -/

theorem loadStep (q0 q4 : XReg) (k : Nat) (s : State) (h : q0 ≠ .xmm8 ∧ q4 ≠ .xmm8 ∧ q0 ≠ q4)
    (h1 : InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) k) 16)
    (h2 : InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) (k + 4)) 16) :
    ∃ s', runBlock isa [ldx q0 (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv q4 q0, unpckl q0 .xmm8, unpckh q4 .xmm8] s = some s' ∧
      (∀ l < 2, qword (s'.xmm q0) l = s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l)) 64) ∧
      (∀ l < 2, qword (s'.xmm q4) l = s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 8) 64) ∧
      (∀ x, x ≠ q0 → x ≠ q4 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2, a3⟩ := h
  have hrun : runBlock isa [ldx q0 (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv q4 q0, unpckl q0 .xmm8, unpckh q4 .xmm8] s =
      some ((XOp.bin .punpckhqdq q4 .xmm8).exec ((XOp.bin .punpcklqdq q0 .xmm8).exec ((XOp.bin .movdqa q4 q0).exec
        ((s.setXmm q0 (s.mem.readW (bufAddr (s.gpr .r9) k) 128)).setXmm .xmm8
          (s.mem.readW (bufAddr (s.gpr .r9) (k + 4)) 128))))) := by
    rw [bufAddr] at h1 h2
    simp only [ldx, mv, unpckl, unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
      ea_slot, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, bufAddr, h1, h2, ite_true, Option.map_some]
  refine ⟨_, hrun, fun l hl => ?_, fun l hl => ?_, fun x c d e => ?_, by simp only [XOp.exec, gpr_setXmm],
    by simp only [XOp.exec, mem_setXmm], by simp only [XOp.exec, rd_setXmm], by simp only [XOp.exec, wr_setXmm]⟩
  · simp only [XOp.exec, xmm_setXmm, a1, a3, a1.symm, a2.symm, ite_true, ite_false]
    rw [qword_unpckl _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]; rw [qword_readW _ _ (by decide)]; simp
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]; simp
  · simp only [XOp.exec, xmm_setXmm, a1, a2.symm, a3.symm, a1.symm, ite_true, ite_false]
    rw [qword_unpckh _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true, XBinOp.eval]; rw [qword_readW _ _ (by decide)]; simp
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]
  · simp only [XOp.exec, xmm_setXmm, c, d, e, ite_false]

theorem q_ne : ∀ i < 8, q i ≠ .xmm8 ∧ q i ≠ .xmm9 ∧ ∀ j < 8, q i = q j → i = j := by decide

theorem loadSteps (s : State) (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (bufAddr (s.gpr .r9) i) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun k =>
        [ldx (q k) (bufSlot k), ldx .xmm8 (bufSlot (k + 4)), mv (q (k + 4)) (q k), unpckl (q k) .xmm8,
          unpckh (q (k + 4)) .xmm8]) s = some s' ∧
      (∀ l < 2, ∀ k < n, ∀ h < 2, lane q s' l (k + 4 * h) =
        s.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j hj => absurd hj (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := ih (by omega)
    obtain ⟨s2, e2, ha, hb, hc, g2, m2, r2, w2⟩ := loadStep (q n) (q (n + 4)) n s1
      ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1, fun h => by have := (q_ne n (by omega)).2.2 _ (by omega) h; omega⟩
      (by rw [r1, w1, g1]; exact hin _ (by omega)) (by rw [r1, w1, g1]; exact hin _ (by omega))
    refine ⟨s2, ?_, fun l hl k hk h hh => ?_, g2.trans g1, m2.trans m1, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · rw [g1, m1] at ha hb
      by_cases hk' : k = n
      · subst hk'
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
        · simpa [lane] using ha l hl
        · simpa [lane] using hb l hl
      · have := h1 l hl k (by omega) h hh
        simp only [lane] at this ⊢
        rw [hc _ (fun e => by have := (q_ne _ (by omega)).2.2 _ (by omega) e; omega)
          (fun e => by have := (q_ne _ (by omega)).2.2 _ (by omega) e; omega) (q_ne _ (by omega)).1, this]

/-- The buffer's bytes, in the halves of its blocks. -/
theorem half_bit {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State} (h : BufIs m b S) {i n j : Nat} (hi : i < 8)
    (hn : n < 16) (hj : j < 8) :
    (m.readW (bufAddr b i + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) = ((S i).getD n 0).getLsbD j := by
  rw [Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and, getLsbD_read _ _ (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (n / 8) + (8 * (n % 8) + j) / 8 = n by omega, h i hi n hn,
    show (8 * (n % 8) + j) % 8 = j by omega]

theorem toBs_bits {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State}
    (hq : ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (lane q s l (k + 4 * (n / 8))).getLsbD (8 * (n % 8) + j) = ((S (4 * l + k)).getD n 0).getLsbD j) :
    ∃ s', runBlock isa toBs s = some s' ∧ Keep s s' ∧ Holds false q s' S := by
  obtain ⟨s', e, k, h⟩ := layer_ok toBs_check (by decide +kernel) (by decide) he
  refine ⟨s', e, k, fun l hl j hj n hn k hk => ?_⟩
  rw [h l hl j hj _ (Nat.lt_of_lt_of_le (posAt_lt false hn hk) (by decide))]
  simp only [toBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_posAt false hn hk,
    posAt_mod false n hk]
  exact hq l hl k hk n hn j hj

theorem toBs_holds {s : State} (he : Env0 s) {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State} (hB : BufIs m b S)
    (hq : ∀ l < 2, ∀ k < 4, ∀ h < 2, lane q s l (k + 4 * h) =
      m.readW (bufAddr b (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64) :
    ∃ s', runBlock isa toBs s = some s' ∧ Keep s s' ∧ Holds false q s' S :=
  toBs_bits he fun l hl k hk n hn j hj => by
    rw [hq l hl k hk _ (by omega), half_bit hB (by omega) hn hj, Nat.add_comm k]

theorem fromBs_bits {s : State} (he : Env0 s) {S : Nat → Spec.Aes.State} (hS : Holds false q s S) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Keep s s' ∧ ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (lane q s' l (k + 4 * (n / 8))).getLsbD (8 * (n % 8) + j) = ((S (4 * l + k)).getD n 0).getLsbD j := by
  obtain ⟨s', e, k, h⟩ := layer_ok fromBs_check (by decide +kernel) (by decide) he
  refine ⟨s', e, k, fun l hl k hk n hn j hj => ?_⟩
  rw [h l hl _ (by omega) _ (by omega)]
  simp only [fromBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
  rw [show (8 * (n % 8) + j) % 8 = j by omega, show (8 * ((k + 4 * (n / 8)) / 4) + (8 * (n % 8) + j) / 8) = n by omega,
    show (k + 4 * (n / 8)) % 4 = k by omega]
  exact hS l hl j hj n hn k hk

/-! ## Storing the buffer -/

theorem readW_writeW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem storeStep (q0 q4 : XReg) (k : Nat) (hk : k < 4) (s : State) (h : q0 ≠ .xmm8 ∧ q4 ≠ .xmm8 ∧ q0 ≠ q4)
    (h1 : InRegions s.wr (bufAddr (s.gpr .r9) k) 16)
    (h2 : InRegions s.wr (bufAddr (s.gpr .r9) (k + 4)) 16) :
    ∃ s', ∃ A B : BitVec 128, runBlock isa [mv .xmm8 q0, unpckl .xmm8 q4, unpckh q0 q4, stx (bufSlot k) .xmm8, stx (bufSlot (k + 4)) q0] s =
        some s' ∧
      s'.mem = (s.mem.writeW (bufAddr (s.gpr .r9) k) A).writeW (bufAddr (s.gpr .r9) (k + 4)) B ∧
      (∀ l < 2, ∀ h < 2, s'.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64 =
        qword (s.xmm (if h = 0 then q0 else q4)) l) ∧
      (∀ x, x ≠ q0 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨A, hA⟩ : ∃ A, A = XBinOp.eval .punpcklqdq (s.xmm q0) (s.xmm q4) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = XBinOp.eval .punpckhqdq (s.xmm q0) (s.xmm q4) := ⟨_, rfl⟩
  have hrun : ∃ s', runBlock isa [mv .xmm8 q0, unpckl .xmm8 q4, unpckh q0 q4, stx (bufSlot k) .xmm8, stx (bufSlot (k + 4)) q0] s =
      some s' ∧ s'.mem = (s.mem.writeW (bufAddr (s.gpr .r9) k) A).writeW (bufAddr (s.gpr .r9) (k + 4)) B ∧
      (∀ x, x ≠ q0 → x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [bufAddr] at h1 h2
    subst hA hB
    simp only [stx, mv, unpckl, unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128,
      XOp.exec, ea_slot, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h1, h2, ite_true, xmm_setXmm, a1, a2, a1.symm,
      ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun x c d => ?_, trivial, trivial, trivial⟩
    simp only [c, d, ite_false]
  obtain ⟨s', hr, hm, hx, hg, hrd, hwr⟩ := hrun
  refine ⟨s', A, B, hr, hm, fun l hl h hh => ?_, hx, hg, hrd, hwr⟩
  have hsep : Mem.Sep (bufAddr (s.gpr .r9) k) (128 / 8) (bufAddr (s.gpr .r9) (k + 4)) (128 / 8) :=
    Offset.sep _ (.inl (by simp only [bufSlot]; omega)) (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
  rw [← qword_readW _ _ hh, hm]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [show k + 4 * 0 = k by omega, Mem.readW_writeW_sep hsep (by decide), readW_writeW_self128, hA]
    rw [qword_unpckl _ _ hh]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp
  · rw [show k + 4 * 1 = k + 4 by omega, readW_writeW_self128, hB]
    rw [qword_unpckh _ _ hh]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp

/-- The buffer. -/
def bufR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 288, 128⟩

theorem buf_contains (b : Addr) {i : Nat} (hi : i < 8) : (bufR b).Contains (bufAddr b i) 16 :=
  Offset.contains _ (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega) (by decide)

theorem storeSteps (s : State) (hin : ∀ i < 8, InRegions s.wr (bufAddr (s.gpr .r9) i) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap fun k =>
        [mv .xmm8 (q k), unpckl .xmm8 (q (k + 4)), unpckh (q k) (q (k + 4)), stx (bufSlot k) .xmm8,
          stx (bufSlot (k + 4)) (q k)]) s = some s' ∧
      (∀ l < 2, ∀ k < n, ∀ h < 2, s'.mem.readW (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) 64 =
        lane q s l (k + 4 * h)) ∧
      (∀ j < 8, n ≤ j % 4 → s'.xmm (q j) = s.xmm (q j)) ∧
      s'.gpr = s.gpr ∧ Frame [bufR (s.gpr .r9)] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun l _ j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, Frame.refl _ _, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, x1, g1, f1, r1, w1⟩ := ih (by omega)
    obtain ⟨s2, A, B, e2, hm, ha, hc, g2, r2, w2⟩ := storeStep (q n) (q (n + 4)) n (by omega) s1
      ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1, fun h => by have := (q_ne n (by omega)).2.2 _ (by omega) h; omega⟩
      (by rw [w1, g1]; exact hin _ (by omega)) (by rw [w1, g1]; exact hin _ (by omega))
    rw [g1] at hm ha
    refine ⟨s2, ?_, fun l hl k hk h hh => ?_, fun j hj hnj => ?_, g2.trans g1, ?_, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · by_cases hk' : k = n
      · subst hk'
        rw [ha l hl h hh, lane]
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
        · simp only [ite_true, Nat.mul_zero, Nat.add_zero, x1 k (by omega) (by omega)]
        · simp only [Nat.one_ne_zero, ite_false, Nat.mul_one, x1 (k + 4) (by omega) (by omega)]
      · rw [← h1 l hl k (by omega) h hh, hm]
        have sep : ∀ i < 8, i ≠ k + 4 * l → Mem.Sep (bufAddr (s.gpr .r9) (k + 4 * l) + BitVec.ofNat 64 (8 * h)) (64 / 8)
            (bufAddr (s.gpr .r9) i) (128 / 8) := fun i hi hne => by
          simp only [bufAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact Offset.sep _ (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
        rw [Mem.readW_writeW_sep (sep _ (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (sep _ (by omega) (by omega)) (by decide)]
    · rw [hc _ (fun e => by have := (q_ne j hj).2.2 _ (by omega) e; omega) (q_ne j hj).1, x1 j hj (by omega)]
    · rw [hm]
      exact (f1.writeW List.mem_cons_self _ (buf_contains _ (by omega))).writeW List.mem_cons_self _
        (buf_contains _ (by omega))

theorem bufIs_of {m : Mem} {b : Addr} {S : Nat → Spec.Aes.State}
    (h : ∀ l < 2, ∀ k < 4, ∀ n < 16, ∀ j < 8,
      (m.readW (bufAddr b (k + 4 * l) + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) =
        ((S (4 * l + k)).getD n 0).getLsbD j) : BufIs m b S := fun i hi n hn => byte_ext fun j hj => by
  have := h (i / 4) (by omega) (i % 4) (by omega) n hn j hj
  rw [show 4 * (i / 4) + i % 4 = i by omega, show i % 4 + 4 * (i / 4) = i by omega] at this
  rw [← this, Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
    getLsbD_read _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (n / 8) + (8 * (n % 8) + j) / 8 = n by omega, show (8 * (n % 8) + j) % 8 = j by omega]

/-! ## The cipher on the buffer -/

/-- The cipher after the first round key and `m` middle rounds. -/
def encMid (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) (Spec.Aes.addRoundKey x (Spec.Aes.roundKey w 0))

theorem encMid_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    encMid w (m + 1) x = rnd w (m + 1) (encMid w m x) := by
  simp [encMid, List.range_succ, List.foldl_append]

theorem cipher_encMid (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    Spec.Aes.cipher nr w x = Spec.Aes.addRoundKey (Spec.Aes.shiftRows (Spec.Aes.subBytes (encMid w (nr - 1) x)))
      (Spec.Aes.roundKey w nr) := rfl

variable {b : Addr} {nr : Nat} {w : List Byte}

/-- What a batch needs: the round keys, and the buffer. -/
structure BatchPre (b : Addr) (nr : Nat) (w : List Byte) (S : Nat → Spec.Aes.State) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  r9 : s.gpr .r9 = b
  rsi : s.gpr .rsi = BitVec.ofNat 64 nr
  buf : BufIs s.mem b S

/-- What a batch leaves. -/
structure BatchPost (b : Addr) (nr : Nat) (w : List Byte) (S : Nat → Spec.Aes.State) (s s' : State) : Prop where
  ready : Ready b nr w s'.mem s'.rd s'.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b, 416⟩] s.mem s'.mem
  buf : BufIs s'.mem b S

theorem BatchPre.env {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) : Env0 s where
  ok := ⟨fun k hk => by
    rw [show s.gpr cfg.base = b from h.r9]
    exact h.ready.inWr (by simp only [cfg] at hk; omega), by decide⟩
  masks := by rw [h.r9]; exact h.ready.masks

theorem Ready.bufIn {m : Mem} {rd wr : List Region} (h : Ready b nr w m rd wr) {i : Nat} (hi : i < 8) :
    InRegions wr (bufAddr b i) 16 := h.inWr (by simp only [bufSlot]; omega)

/-- The buffer loaded and transposed. -/
theorem loadBuf_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa (.block (loadBuf ++ toBs)) s fun s' => Keep s s' ∧ Holds false q s' S := by
  obtain ⟨s1, e1, h1, g1, m1, r1, w1⟩ := loadSteps s (fun i hi => by
    rw [h.r9]
    obtain ⟨R, hR, hc⟩ := h.ready.bufIn hi
    exact ⟨R, List.mem_append_right _ hR, hc⟩) 4 (by decide)
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2⟩ := toBs_holds k1.env h.buf (by rw [h.r9] at h1; exact h1)
  refine WP.block_append (WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, k1.trans k2, h2⟩⟩)

/-- The states to the buffer. -/
theorem storeBuf_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} 
    (h : RS s₁ b nr w cnt i false q S s) :
    WP isa (.block (fromBs ++ storeBuf)) s (BatchPost b nr w S s₁) := by
  obtain ⟨s2, e2, k2, h2⟩ := fromBs_bits h.env h.holds
  have hf2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hready2 : Ready b nr w s2.mem s2.rd s2.wr := by
    refine ⟨by rw [k2.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩
    · refine (h.ready.keys i hi).congrW fun j hj => ?_
      have := h.ready.nrs
      rw [hf2.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
      rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
    · have := k2.env.masks
      rwa [k2.gpr, h.r9] at this
  have h9 : s2.gpr .r9 = b := by rw [k2.gpr, h.r9]
  obtain ⟨s3, e3, h3, -, g3, f3, r3, w3⟩ := storeSteps s2 (fun i hi => by rw [h9]; exact hready2.bufIn hi) 4 (by decide)
  rw [h9] at h3 f3
  refine WP.block_append (WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, ?_⟩⟩)
  refine ⟨?_, fun x a c => by rw [g3, k2.gpr, h.gpr x a c], (r3.trans k2.rd).trans h.rd, (w3.trans k2.wr).trans h.wr,
    ?_, bufIs_of fun l hl k hk n hn j hj => ?_⟩
  · rw [r3, w3]
    refine hready2.frame f3 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (.inr (by decide)) (by decide) (by decide),
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)⟩
  · have sub : ∀ r ∈ [(⟨b, 288⟩ : Region), bufR b], ∃ r' ∈ [(⟨b, 416⟩ : Region)], Region.Sub r r' := by
      intro r hr
      refine ⟨_, List.mem_singleton.mpr rfl, fun x hx => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains] at hx ⊢; omega
      · simp only [Region.Contains, bufR] at hx ⊢; bv_omega
    have a1 := (h.frame.trans hf2).sub (rs' := [⟨b, 416⟩]) fun r hr => sub r (by simp_all)
    exact a1.trans (f3.sub fun r hr => sub r (by simp_all))
  · rw [h3 l hl k hk _ (by omega), h2 l hl k hk n hn j hj]

theorem sh1 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 →
    (BitVec.ofNat 64 n >>> (1 : Nat) : BitVec 64) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (n / 2 - 1) := by
  rintro n (rfl | rfl | rfl) <;> decide

theorem keyAddr_zero (b : Addr) : keyAddr b 0 = b + BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) := rfl

/-- The registers a batch's setup writes. -/
theorem setup_ok {S T : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1)
    (hh : Holds false q s1 T) :
    WP isa (.block (pairs ++ ([.mov kp (.reg .r9), .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr))) s1
      (RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1)) 0 false q T) := by
  have hsi : s1.gpr .rsi = BitVec.ofNat 64 nr := by rw [k.gpr, h.rsi]
  have h9 : s1.gpr .r9 = b := by rw [k.gpr, h.r9]
  have hf : Frame [⟨b, 288⟩] s.mem s1.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hready : Ready b nr w s1.mem s1.rd s1.wr := by
    refine ⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩
    · refine (h.ready.keys i hi).congrW fun j hj => ?_
      have := h.ready.nrs
      rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
      rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
    · have := k.env.masks
      rwa [k.gpr, h.r9] at this
  apply WP.of_runBlock
  simp only [pairs, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, execShift, readSrc, Option.bind_some, Option.map_some, show kp = Reg.rax from rfl, Nat.le_refl,
    Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left', gpr_setReg, gpr_arithFlags, gpr_setFlags,
    reduceCtorEq, ite_false, hsi, h9]
  refine ⟨hready, ?_, fun x a c => ?_, ?_, ?_, k.rd, k.wr, hf, hh⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, h9]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, ite_false, k.gpr]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact sh1 nr h.ready.nrs
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact (keyAddr_zero b).symm

theorem beq_zero {c : Nat} (hc : c < 2 ^ 64) : (BitVec.ofNat 64 c == 0) = decide (c = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [Nat.mod_eq_of_lt hc] using this
  · rintro rfl; rfl

/-- The loop counter counted down. -/
theorem RS.count {s₁ s : State} {c i : Nat} {r : Nat → XReg} {S : Nat → Spec.Aes.State} {f : Bool}
    (h : RS s₁ b nr w (BitVec.ofNat 64 (c + 1)) i f r S s) (hc : c < 2 ^ 32) :
    WP isa (.block ([.alu .sub .r10 (.imm 1)] : List Instr)) s fun s' =>
      RS s₁ b nr w (BitVec.ofNat 64 c) i f r S s' ∧ X86_64.eval .ne s' = some (decide (c ≠ 0)) := by
  apply WP.of_runBlock
  have e : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
    rw [h.cnt, show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, readSrc, Option.bind_some, Option.some.injEq, exists_eq_left', e]
  refine ⟨⟨h.ready, ?_, fun x a d => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, d, ite_false]; exact h.gpr x a d
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, h.kpAt]
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem encPair_ok {s₁ s : State} {cnt : BitVec 64} {m : Nat} {S : Nat → Spec.Aes.State} (hm : 2 * m + 2 ≤ nr)
    (h : RS s₁ b nr w cnt (2 * m + 1) false q (fun k => encMid w (2 * m) (S k)) s) :
    WP isa (.block (roundA ++ roundB)) s (RS s₁ b nr w cnt (2 * (m + 1) + 1) false q fun k => encMid w (2 * (m + 1)) (S k)) := by
  refine WP.block_append (WP.mono (roundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.mono (roundB_ok (by omega) (by omega) (by omega) h2) fun s3 h3 => h3.congr fun k _ => ?_
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, encMid_succ, encMid_succ]

theorem moveBack_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} {f : Bool}
    (h : RS s₁ b nr w cnt i f p S s) : WP isa (.block moveBack) s (RS s₁ b nr w cnt i f q S) := by
  obtain ⟨s', e, k, hb⟩ := layer_ok move_check (by decide +kernel) (by decide) h.env
  refine h.step ⟨s', e, k, fun l hl => ?_⟩
  refine (h.holds l hl).congrW fun j hj => BitVec.eq_of_getLsbD_eq fun x hx => ?_
  rw [hb l hl j hj x hx]
  simp [termsXor, idT]

/-- The last two rounds. -/
theorem encFin_ok {s₁ s : State} {cnt : BitVec 64} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt (nr - 1) false q (fun k => encMid w (nr - 2) (S k)) s) :
    WP isa (.block (roundA ++ lastB)) s (RS s₁ b nr w cnt nr false q fun k => Spec.Aes.cipher nr w (S k)) := by
  have hn := h.ready.nrs
  refine WP.block_append (WP.mono (roundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h2.step (sub_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.step (sr2_holds h3.env h3.holds)) fun s4 h4 => ?_
  rw [show nr - 1 + 1 = nr by omega] at h4
  refine WP.mono (h4.ark regs_p (by rcases hn with rfl | rfl | rfl <;> rfl) (Nat.le_refl _)) fun s5 h5 => ?_
  refine WP.mono (moveBack_ok h5) fun s6 h6 => h6.congr fun k _ => ?_
  rw [kr, ite_eq_right (by omega), lastRound63 _ (h.ready.len nr (Nat.le_refl _)), cipher_encMid,
    show nr - 1 = (nr - 2) + 1 by omega, encMid_succ]

theorem encLast_ok {s₁ s : State} {cnt : BitVec 64} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt (nr - 1) false q (fun k => encMid w (nr - 2) (S k)) s) :
    WP isa (.block (roundA ++ lastB ++ fromBs ++ storeBuf)) s (BatchPost b nr w (fun k => Spec.Aes.cipher nr w (S k)) s₁) := by
  rw [List.append_assoc]
  exact WP.block_append (WP.mono (encFin_ok h) fun _ h6 => storeBuf_ok h6)

/-- The pairs of rounds before the last, from the first round key on. -/
theorem encLoop_ok {s₁ s : State} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w (BitVec.ofNat 64 (nr / 2 - 1)) 1 false q (fun k => Spec.Aes.addRoundKey (S k) (kr w 0)) s) :
    WP isa (.loop (.block (roundA ++ roundB ++ ([.alu .sub .r10 (.imm 1)] : List Instr))) .ne) s
      (RS s₁ b nr w 0 (nr - 1) false q fun k => encMid w (nr - 2) (S k)) := by
  have hn := h.ready.nrs
  let I : Nat → State → Prop := fun c s' => ∃ m, c = nr / 2 - 1 - m ∧ m < nr / 2 - 1 ∧
    RS s₁ b nr w (BitVec.ofNat 64 (nr / 2 - 1 - m)) (2 * m + 1) false q (fun k => encMid w (2 * m) (S k)) s'
  refine WP.loop (M := isa) I ?_ (nr / 2 - 1) s ⟨0, rfl, by omega, h.congr fun k _ => rfl⟩
  rintro c s' ⟨m, rfl, hm, hs'⟩
  refine WP.block_append (WP.mono (encPair_ok (by omega) hs') fun s6 h6 => ?_)
  rw [show nr / 2 - 1 - m = (nr / 2 - 1 - (m + 1)) + 1 by omega] at h6
  refine WP.mono (h6.count (by omega)) fun s7 ⟨h7, hz⟩ => ?_
  by_cases hl : nr / 2 - 1 - (m + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    have e1 : 2 * (m + 1) + 1 = nr - 1 := by omega
    have e2 : 2 * (m + 1) = nr - 2 := by omega
    rw [hl, e1, e2] at h7
    exact h7
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h7⟩

theorem encrypt8_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa encrypt8 s (BatchPost b nr w (fun k => Spec.Aes.cipher nr w (S k)) s) := by
  refine WP.seq ?_
  rw [List.append_assoc (loadBuf ++ toBs) pairs]
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (loadBuf_ok h) fun s1 ⟨k1, h1⟩ => ?_
  refine WP.mono (setup_ok h k1 h1) fun s2 h2 => ?_
  refine WP.mono (h2.ark regs_q rfl (Nat.zero_le _)) fun s3 h3 => ?_
  refine WP.mono h3.next fun s4 h4 => ?_
  exact WP.seq (WP.mono (encLoop_ok h4) fun s5 h5 => encLast_ok h5)

/-! ## The inverse cipher on the buffer -/

theorem shl6 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 → (BitVec.ofNat 64 n <<< (6 : Nat) : BitVec 64) = BitVec.ofNat 64 (64 * n) := by
  rintro n (rfl | rfl | rfl) <;> decide

theorem Keep.ready {S : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1) :
    Frame [⟨b, 288⟩] s.mem s1.mem ∧ Ready b nr w s1.mem s1.rd s1.wr := by
  have hf : Frame [⟨b, 288⟩] s.mem s1.mem := by
    have := k.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine ⟨hf, ⟨by rw [k.wr]; exact h.ready.sc, fun i hi => ?_, ?_, h.ready.nrs, h.ready.len⟩⟩
  · refine (h.ready.keys i hi).congrW fun j hj => ?_
    have := h.ready.nrs
    rw [hf.readW (r := ⟨b + BitVec.ofNat 64 keysOff, 960⟩) ?_ (low_disj b) (by decide)]
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega) (by decide)
  · have := k.env.masks
    rwa [k.gpr, h.r9] at this

theorem keyAddr_last (b : Addr) (n : Nat) :
    keyAddr b n = BitVec.ofNat 64 (64 * n) + b + BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) := by
  rw [keyAddr, show BitVec.signExtend 64 (BitVec.ofNat 32 keysOff) = BitVec.ofNat 64 keysOff by decide,
    BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 (64 * n)) b, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 keysOff)]

theorem setupDec_ok {S : Nat → Spec.Aes.State} {s s1 : State} (h : BatchPre b nr w S s) (k : Keep s s1)
    (hh : Holds false q s1 S) :
    WP isa (.block (pairs ++ ([.mov kp (.reg .rsi), .shift .shl kp 6, .alu .add kp (.reg .r9),
        .alu .add kp (.imm (BitVec.ofNat 32 keysOff))] : List Instr))) s1
      (RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1)) nr false q S) := by
  have hsi : s1.gpr .rsi = BitVec.ofNat 64 nr := by rw [k.gpr, h.rsi]
  have h9 : s1.gpr .r9 = b := by rw [k.gpr, h.r9]
  obtain ⟨hf, hready⟩ := Keep.ready h k
  apply WP.of_runBlock
  simp only [pairs, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    execAlu, execShift, readSrc, Option.bind_some, Option.map_some, show kp = Reg.rax from rfl, Nat.le_refl,
    Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left', gpr_setReg, gpr_arithFlags, gpr_setFlags,
    reduceCtorEq, ite_false, hsi, h9]
  refine ⟨hready, ?_, fun x a c => ?_, ?_, ?_, k.rd, k.wr, hf, hh⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, h9]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, ite_false, k.gpr]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true]
    exact sh1 nr h.ready.nrs
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, shl6 nr h.ready.nrs]
    exact (keyAddr_last b nr).symm

theorem RS.prev {s₁ s : State} {cnt : BitVec 64} {i : Nat} {r : Nat → XReg}
    {S : Nat → Spec.Aes.State} {f : Bool} (h : RS s₁ b nr w cnt (i + 1) f r S s) :
    WP isa (.block [prevKey]) s (RS s₁ b nr w cnt i f r S) := by
  apply WP.of_runBlock
  have e : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  simp only [prevKey, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, e, Option.bind_some,
    Option.some.injEq, exists_eq_left', show kp = Reg.rax from rfl]
  refine ⟨h.ready, ?_, fun x a c => ?_, ?_, ?_, h.rd, h.wr, h.frame, h.holds⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.r9
  · rw [gpr_setReg_of_ne _ _ a, gpr_arithFlags]; exact h.gpr x a c
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags]; exact h.cnt
  · rw [gpr_setReg_self, h.kpAt, keyAddr, keyAddr, show keysOff + 64 * (i + 1) = keysOff + 64 * i + 64 by omega,
      BitVec.ofNat_add (keysOff + 64 * i), ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _

/-- A round of the inverse cipher, between states with `{63}` added. -/
def irnd0 (w : List Byte) (i : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  Spec.Aes.invMixColumns (Spec.Aes.addRoundKey ((Spec.Aes.invShiftRows x).map invSbox0) (kr w i))

theorem irnd0_c63 {i j : Nat} (h0 : i ≠ 0) (hl : (Spec.Aes.roundKey w i).length = 16) (hj : i = nr - 1 - j)
    (x : Spec.Aes.State) : irnd0 w i (c63 x) = c63 (irnd nr w j x) := by
  rw [irnd0, kr, ite_eq_right h0, invRound63 _ hl, irnd, hj]

theorem invRoundA_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 0) (hn : i + 1 ≤ nr)
    (h : RS s₁ b nr w cnt (i + 1) false q S s) :
    WP isa (.block invRoundA) s (RS s₁ b nr w cnt i true q fun k => irnd0 w (i + 1) (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (h.step (invSr2_holds h.env h.holds)) fun s2 h2 => ?_
  refine WP.mono (h2.step (invSub_holds h2.env h2.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p (by simp; omega) hn) fun s4 h4 => ?_
  refine WP.mono (h4.step (invMc_holds true h4.env h4.holds)) fun s5 h5 => ?_
  exact h5.prev

theorem invRoundB_ok {s₁ s : State} {cnt : BitVec 64} {i : Nat} {S : Nat → Spec.Aes.State} (hi : i % 2 = 1) (hn : i + 1 ≤ nr)
    (h : RS s₁ b nr w cnt (i + 1) true q S s) :
    WP isa (.block invRoundB) s (RS s₁ b nr w cnt i false q fun k => irnd0 w (i + 1) (S k)) := by
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h.skipInv.step (invSub_holds h.env h.skipInv.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p (by simp; omega) hn) fun s4 h4 => ?_
  refine WP.mono (h4.step (invMc_holds false h4.env h4.holds)) fun s5 h5 => ?_
  exact h5.prev

/-- The states before the pair of rounds `m`. -/
def decMid (nr : Nat) (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  c63 (invMid nr w m (Spec.Aes.addRoundKey x (Spec.Aes.roundKey w nr)))

theorem decPair_ok {s₁ s : State} {cnt : BitVec 64} {m : Nat} {S : Nat → Spec.Aes.State} (hm : 2 * m + 4 ≤ nr)
    (h : RS s₁ b nr w cnt (nr - 1 - 2 * m) false q (fun k => decMid nr w (2 * m) (S k)) s) :
    WP isa (.block (invRoundA ++ invRoundB)) s
      (RS s₁ b nr w cnt (nr - 1 - 2 * (m + 1)) false q fun k => decMid nr w (2 * (m + 1)) (S k)) := by
  have hn := h.ready.nrs
  have e1 : nr - 1 - 2 * m = nr - 1 - 2 * (m + 1) + 1 + 1 := by omega
  rw [e1] at h
  refine WP.block_append (WP.mono (invRoundA_ok (by omega) (by omega) h) fun s2 h2 => ?_)
  refine WP.mono (invRoundB_ok (by omega) (by omega) h2) fun s3 h3 => h3.congr fun k _ => ?_
  simp only [decMid]
  rw [irnd0_c63 (nr := nr) (j := 2 * m) (by omega) (h.ready.len _ (by omega)) (by omega),
    irnd0_c63 (nr := nr) (j := 2 * m + 1) (by omega) (h.ready.len _ (by omega)) (by omega),
    show 2 * (m + 1) = 2 * m + 1 + 1 by omega, invMid_succ, invMid_succ]

theorem decLast_ok {s₁ s : State} {cnt : BitVec 64} {S : Nat → Spec.Aes.State}
    (h : RS s₁ b nr w cnt 1 false q (fun k => decMid nr w (nr - 2) (S k)) s) :
    WP isa (.block (invRoundA ++ invLastB ++ fromBs ++ storeBuf)) s
      (BatchPost b nr w (fun k => Spec.Aes.invCipher nr w (S k)) s₁) := by
  have hn := h.ready.nrs
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (invRoundA_ok (i := 0) rfl (by omega) h) fun s2 h2 => ?_)
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (h2.skipInv.step (invSub_holds h2.env h2.skipInv.holds)) fun s3 h3 => ?_
  refine WP.mono (h3.ark regs_p rfl (Nat.zero_le _)) fun s5 h5 => ?_
  refine WP.mono (moveBack_ok h5) fun s6 h6 => ?_
  refine storeBuf_ok (h6.congr fun k _ => ?_)
  simp only [decMid]
  rw [irnd0_c63 (nr := nr) (j := nr - 2) (by omega) (h.ready.len _ (by omega)) (by omega), invShiftRows_c63,
    map_invSbox0, kr, ite_eq_left rfl, invCipher_eq, show nr - 1 = (nr - 2) + 1 by omega, invMid_succ]

theorem decrypt8_ok {S : Nat → Spec.Aes.State} {s : State} (h : BatchPre b nr w S s) :
    WP isa decrypt8 s (BatchPost b nr w (fun k => Spec.Aes.invCipher nr w (S k)) s) := by
  have hn := h.ready.nrs
  refine WP.seq ?_
  rw [List.append_assoc (loadBuf ++ toBs) pairs]
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine WP.mono (loadBuf_ok h) fun s1 ⟨k1, h1⟩ => ?_
  refine WP.mono (setupDec_ok h k1 h1) fun s2 h2 => ?_
  refine WP.mono (h2.ark regs_q (by rcases hn with rfl | rfl | rfl <;> rfl) (Nat.le_refl _)) fun s3 h3 => ?_
  rw [show nr = nr - 1 + 1 by omega] at h3
  refine WP.mono h3.prev fun s4 h4 => ?_
  rw [← show nr = nr - 1 + 1 by omega] at h4
  refine WP.seq (WP.mono (Q := RS s b nr w 0 1 false q fun k => decMid nr w (nr - 2) (S k)) ?_
    fun s5 h5 => decLast_ok h5)
  let I : Nat → State → Prop := fun c s' => ∃ m, c = nr / 2 - 1 - m ∧ m < nr / 2 - 1 ∧
    RS s b nr w (BitVec.ofNat 64 (nr / 2 - 1 - m)) (nr - 1 - 2 * m) false q (fun k => decMid nr w (2 * m) (S k)) s'
  refine WP.loop (M := isa) I ?_ (nr / 2 - 1) s4 ⟨0, rfl, by omega, h4.congr fun k _ => ?_⟩
  · rintro c s' ⟨m, rfl, hm, hs'⟩
    refine WP.block_append (WP.mono (decPair_ok (by omega) hs') fun s6 h6 => ?_)
    rw [show nr / 2 - 1 - m = (nr / 2 - 1 - (m + 1)) + 1 by omega] at h6
    refine WP.mono (h6.count (by omega)) fun s7 ⟨h7, hz⟩ => ?_
    by_cases hl : nr / 2 - 1 - (m + 1) = 0
    · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
      have e1 : nr - 1 - 2 * (m + 1) = 1 := by omega
      have e2 : 2 * (m + 1) = nr - 2 := by omega
      rw [hl, e1, e2] at h7
      exact h7
    · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h7⟩
  · rw [kr, ite_eq_right (by omega), addRoundKey_rk63 _ (h.ready.len nr (Nat.le_refl _))]
    rfl

end VG.Proof.Aes.X86_64.Sse

end

section

/-! # The round keys in slices -/

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

/-! ## The masks -/

theorem setMask_ok (k : Nat) (v : BitVec 64) (hk : k < 18) (s : State)
    (hin : InRegions s.wr (xAddr (s.gpr .r9) k) 16) :
    ∃ s', runBlock isa (setMask k v) s = some s' ∧
      (∀ l < 2, qword (s'.mem.readW (xAddr (s.gpr .r9) k) 128) l = v) ∧
      (∀ j < 18, j ≠ k → s'.mem.readW (xAddr (s.gpr .r9) j) 128 = s.mem.readW (xAddr (s.gpr .r9) j) 128) ∧
      Frame [⟨s.gpr .r9, 288⟩] s.mem s'.mem ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [setMask, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    XOp.exec, State.store128, ea_slot, stx, gpr_setXmm, gpr_setReg, reduceCtorEq, ite_false, ite_true, wr_setXmm,
    wr_setReg, hin, mem_setXmm, mem_setReg, xmm_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun j hj hne => ?_, ?_, fun x a => ?_, by first | rfl | trivial, by first | rfl | trivial⟩
  · rw [readW_writeW_self128, qword_unpckl _ _ hl]
    have : ∀ x y : BitVec 64, qword (x ++ y) 0 = y := fun x y => by
      rw [StraightY.qword_app _ _ (by decide)]; simp
    split <;> exact this _ _
  · exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [a, ite_false]

theorem setMasks_eq : setMasks = maskVals.flatMap fun m => setMask m.1 m.2 := by decide

theorem masks_list (l : List (Nat × BitVec 64)) (hn : (l.map (·.1)).Nodup) (hl : ∀ m ∈ l, m.1 < 18) (s : State)
    (hin : ∀ k < 18, InRegions s.wr (xAddr (s.gpr .r9) k) 16) :
    ∃ s', runBlock isa (l.flatMap fun m => setMask m.1 m.2) s = some s' ∧
      (∀ m ∈ l, ∀ i < 2, qword (s'.mem.readW (xAddr (s.gpr .r9) m.1) 128) i = m.2) ∧
      (∀ j < 18, j ∉ l.map (·.1) → s'.mem.readW (xAddr (s.gpr .r9) j) 128 = s.mem.readW (xAddr (s.gpr .r9) j) 128) ∧
      Frame [⟨s.gpr .r9, 288⟩] s.mem s'.mem ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | cons m l ih =>
    obtain ⟨s1, e1, a1, o1, f1, g1, r1, w1⟩ := setMask_ok m.1 m.2 (hl m List.mem_cons_self) s
      (hin _ (hl m List.mem_cons_self))
    have h9 : s1.gpr .r9 = s.gpr .r9 := g1 _ (by decide)
    obtain ⟨s2, e2, a2, o2, f2, g2, r2, w2⟩ := ih (List.nodup_cons.mp hn).2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) s1
      (by rw [w1, h9]; exact hin)
    rw [h9] at a2 o2 f2
    refine ⟨s2, ?_, fun x hx i hi => ?_, fun j hj hne => ?_, f1.trans f2, fun x a => (g2 x a).trans (g1 x a),
      r2.trans r1, w2.trans w1⟩
    · rw [List.flatMap_cons, Interleave.runBlock_append, e1, Option.bind_some, e2]
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [o2 _ (hl x List.mem_cons_self) (List.nodup_cons.mp hn).1]; exact a1 i hi
      · exact a2 x hx i hi
    · simp only [List.map_cons, List.mem_cons, not_or] at hne
      rw [o2 j hj hne.2, o1 j hj hne.1]

/-! ## The schedule's bytes -/

theorem rk_byte (m : Mem) (p : Addr) {nr i n : Nat} (hi : i ≤ nr) (hn : n < 16) :
    (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i).getD n 0 = m (p + BitVec.ofNat 64 (16 * i + n)) := by
  simp only [Spec.Aes.roundKey, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt hn, List.getElem?_drop, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem rk_length (m : Mem) (p : Addr) {nr i : Nat} (hi : i ≤ nr) :
    (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i).length = 16 := by
  simp only [Spec.Aes.roundKey, Spec.Aes.bytesAt, List.length_take, List.length_drop, List.length_map, List.length_range]
  omega

/-- The bits of a half of a round key. -/
theorem key_bit (m : Mem) (p : Addr) {nr i n j : Nat} (hi : i ≤ nr) (hn : n < 16) (hj : j < 8) :
    (m.readW (p + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * (n / 8))) 64).getLsbD (8 * (n % 8) + j) =
      ((rkState (Spec.Aes.roundKey (Spec.Aes.bytesAt m p (16 * (nr + 1))) i)).getD n 0).getLsbD j := by
  rw [getD_rkState _ hn, rk_byte m p hi hn, Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
    getLsbD_read _ _ (by omega), BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show 16 * i + (8 * (n / 8) + (8 * (n % 8) + j) / 8) = 16 * i + n by omega, show (8 * (n % 8) + j) % 8 = j by omega]

/-! ## Loading keys -/

theorem ea_at (s : State) (r : Reg) (d : Nat) : s.ea (Impl.Aes.X86_64.at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, Impl.Aes.X86_64.at_, BitVec.ofInt_natCast]

theorem q_eqs : q 0 = .xmm0 ∧ q 1 = .xmm1 ∧ q 2 = .xmm2 ∧ q 3 = .xmm3 ∧ q 4 = .xmm4 ∧ q 5 = .xmm5 ∧ q 6 = .xmm6 ∧
    q 7 = .xmm7 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The second key's halves in form 1. -/
theorem pick_ok (s : State) :
    ∃ s', runBlock isa keyPick s = some s' ∧
      (∀ l < 2, ∀ h < 2, lane q s' l (4 * h) = lane q s l (4 * h + l)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [keyPick, unpckl, unpckh, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, XOp.exec,
    xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, reduceCtorEq, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', and_self, and_true]
  intro l hl h hh
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp only [lane, q, Nat.mul_zero, Nat.mul_one, Nat.zero_add] <;>
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    simp only [xmm_setXmm, reduceCtorEq, ite_false, ite_true, qword_unpckl _ _ (show 0 < 2 by decide),
      qword_unpckl _ _ (show 1 < 2 by decide), qword_unpckh _ _ (show 0 < 2 by decide), Nat.one_ne_zero, Nat.reduceAdd]

/-- Where a pair's or the last key's halves come from: key `l` is at `r10 + 16 (d l)`. -/
theorem load2_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .r10) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 16) 16) :
    ∃ s', runBlock isa keyLoad2 s = some s' ∧
      (∀ l < 2, ∀ h < 2, qword (s'.xmm (q (4 * h))) l =
        s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (16 * l) + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0' : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 0) 16 := by simpa using h0
  simp only [keyLoad2, mv, unpckl, unpckh, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
    ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h0', h1, ite_true, Option.map_some, XOp.exec, xmm_setXmm,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl h hh => ?_, trivial, trivial, trivial, trivial⟩
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckl _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]; rw [qword_readW _ _ (by decide)]
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]
  · simp only [Nat.mul_one, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckh _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true, XBinOp.eval]; rw [qword_readW _ _ (by decide)]
    · simp only [Nat.one_ne_zero, ite_false]; rw [qword_readW _ _ (by decide)]

theorem load1_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .r10) 16) :
    ∃ s', runBlock isa keyLoad1 s = some s' ∧
      (∀ l < 2, ∀ h < 2, qword (s'.xmm (q (4 * h))) l = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (8 * h)) 64) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0' : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 0) 16 := by simpa using h0
  simp only [keyLoad1, mv, unpckl, unpckh, q, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.load128,
    ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, h0', ite_true, Option.map_some, XOp.exec, xmm_setXmm,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl h hh => ?_, trivial, trivial, trivial, trivial⟩
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckl _ _ hl]
    simp only [ite_self]; rw [qword_readW _ _ (by decide)]; simp
  · simp only [Nat.mul_one, reduceCtorEq, ite_false, ite_true]
    rw [qword_unpckh _ _ hl]
    simp only [ite_self, XBinOp.eval]; rw [qword_readW _ _ (by decide)]; simp

/-! ## Storing keys -/

theorem lowStep (q0 q1 : XReg) (i : Nat) (s : State) (h : q0 ≠ .xmm8 ∧ q1 ≠ .xmm8)
    (hin : InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa [mv .xmm8 q0, unpckl .xmm8 q1, .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr kp + BitVec.ofNat 64 (16 * i)) (XBinOp.eval .punpcklqdq (s.xmm q0) (s.xmm q1)) ∧
      (∀ x, x ≠ .xmm8 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a1, a2⟩ := h
  simp only [mv, unpckl, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128, XOp.exec, ea_at,
    gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, hin, ite_true, xmm_setXmm, a2, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun x c => ?_, trivial, trivial, trivial⟩
  simp only [c, ite_false]

theorem highStep (q0 q1 : XReg) (i : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (64 + 16 * i)) 16) :
    ∃ s', runBlock isa [unpckh q0 q1, .movdquStore (Impl.Aes.X86_64.at_ kp (64 + 16 * i)) q0] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr kp + BitVec.ofNat 64 (64 + 16 * i)) (XBinOp.eval .punpckhqdq (s.xmm q0) (s.xmm q1)) ∧
      (∀ x, x ≠ q0 → s'.xmm x = s.xmm x) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [unpckh, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store128, XOp.exec, ea_at,
    gpr_setXmm, wr_setXmm, mem_setXmm, hin, ite_true, xmm_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun x c => ?_, by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial⟩
  simp only [c, ite_false]

/-- The quadwords of a 16-byte store of two registers' quadwords `l`. -/
theorem store_pair {m : Mem} {a : Addr} {v : BitVec 128} {x y : BitVec 64}
    (hv : ∀ i < 2, qword v i = if i = 0 then x else y) (j : Nat) (hj : j < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * j)) 64 = if j = 0 then x else y := by
  rw [← qword_readW _ _ hj, readW_writeW_self128, hv j hj]

/-- `n` steps of either store, of quadword `l` at `a`. -/
theorem stores_ok (c : Nat → List Instr) (a : State → Addr) (l : Nat)
    (hstep : ∀ i < 4, ∀ s : State, InRegions s.wr (a s + BitVec.ofNat 64 (16 * i)) 16 → ∃ s', ∃ v : BitVec 128,
      runBlock isa (c i) s = some s' ∧ s'.mem = s.mem.writeW (a s + BitVec.ofNat 64 (16 * i)) v ∧
      (∀ j < 2, qword v j = if j = 0 then lane q s l (2 * i) else lane q s l (2 * i + 1)) ∧
      (∀ j < 8, 2 * i + 2 ≤ j → s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (ha : ∀ s s' : State, s'.gpr = s.gpr → a s' = a s)
    (s : State) (hin : ∀ i < 4, InRegions s.wr (a s + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap c) s = some s' ∧
      (∀ j < 2 * n, s'.mem.readW (a s + BitVec.ofNat 64 (8 * j)) 64 = lane q s l j) ∧
      (∀ j < 8, 2 * n ≤ j → s'.xmm (q j) = s.xmm (q j)) ∧
      s'.gpr = s.gpr ∧ Frame [⟨a s, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, Frame.refl _ _, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s1, e1, h1, x1, g1, f1, r1, w1⟩ := ih (by omega)
    have ha1 := ha s s1 g1
    obtain ⟨s2, v, e2, hm, hv, hx, g2, r2, w2⟩ := hstep n (by omega) s1 (by rw [w1, ha1]; exact hin n (by omega))
    rw [ha1] at hm
    refine ⟨s2, ?_, fun j hj => ?_, fun j hj hnj => ?_, g2.trans g1, ?_, r2.trans r1, w2.trans w1⟩
    · rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append, e1, Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, e2]
    · by_cases hj' : j < 2 * n
      · rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), h1 j hj']
      · have := store_pair (m := s1.mem) (a := a s + BitVec.ofNat 64 (16 * n)) hv (j - 2 * n) (by omega)
        rw [← hm, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * n + 8 * (j - 2 * n) = 8 * j by omega] at this
        rw [this]
        rcases (by omega : j = 2 * n ∨ j = 2 * n + 1) with rfl | rfl
        · simp only [Nat.sub_self, ite_true, lane, x1 (2 * n) (by omega) (by omega)]
        · simp only [show 2 * n + 1 - 2 * n = 1 by omega, Nat.one_ne_zero, ite_false, lane, x1 (2 * n + 1) (by omega) (by omega)]
    · rw [hx j hj (by omega), x1 j hj (by omega)]
    · rw [hm]
      exact f1.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem q_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : q i = q j) : i = j := (q_ne i hi).2.2 j hj h

theorem storeLow_ok (s : State) (hin : ∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', runBlock isa storeLow s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 64 = lane q s 0 j) ∧
      (∀ j < 8, s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ Frame [⟨s.gpr .rax, 64⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have key := stores_ok (fun i => [mv .xmm8 (q (2 * i)), unpckl .xmm8 (q (2 * i + 1)),
      .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8]) (fun s => s.gpr .rax) 0
    (fun i hi s h => by
      obtain ⟨s', e, hm, hx, hg, hr, hw⟩ := lowStep (q (2 * i)) (q (2 * i + 1)) i s
        ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1⟩ h
      exact ⟨s', _, e, hm, fun j hj => by rw [qword_unpckl _ _ hj]; rfl, fun j hj _ => hx _ (q_ne j hj).1, hg, hr, hw⟩)
    (fun s s' h => by simp only [h]) s hin
  -- the low store keeps every slice
  have all : ∀ n ≤ 4, ∀ s : State, (∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (16 * i)) 16) →
      ∀ s', runBlock isa ((List.range n).flatMap fun i => [mv .xmm8 (q (2 * i)), unpckl .xmm8 (q (2 * i + 1)),
        .movdquStore (Impl.Aes.X86_64.at_ kp (16 * i)) .xmm8]) s = some s' →
        (∀ j < 8, s'.xmm (q j) = s.xmm (q j)) ∧ s'.gpr = s.gpr ∧ s'.wr = s.wr := by
    intro n
    induction n with
    | zero => intro _ s _ s' e; obtain rfl := Option.some.inj (e : some s = some s'); exact ⟨fun _ _ => rfl, rfl, rfl⟩
    | succ n ih =>
      intro hn s hin s' e
      rw [List.range_succ, List.flatMap_append, Interleave.runBlock_append] at e
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨x1, g1, w1⟩ := ih (by omega) s hin s1 e1
      obtain ⟨s2, e3, -, hx, hg, -, hw⟩ := lowStep (q (2 * n)) (q (2 * n + 1)) n s1
        ⟨(q_ne _ (by omega)).1, (q_ne _ (by omega)).1⟩ (by rw [w1, g1]; exact hin n (by omega))
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, e3] at e2
      obtain rfl := Option.some.inj e2
      exact ⟨fun j hj => (hx _ (q_ne j hj).1).trans (x1 j hj), hg.trans g1, hw.trans w1⟩
  obtain ⟨s', e, h1, -, hg, hf, hr, hw⟩ := key 4 (Nat.le_refl _)
  exact ⟨s', e, h1, (all 4 (Nat.le_refl _) s hin s' e).1, hg, hf, hr, hw⟩

theorem storeHigh_ok (s : State) (hin : ∀ i < 4, InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (64 + 16 * i)) 16) :
    ∃ s', runBlock isa storeHigh s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rax + BitVec.ofNat 64 64 + BitVec.ofNat 64 (8 * j)) 64 = lane q s 1 j) ∧
      s'.gpr = s.gpr ∧ Frame [⟨s.gpr .rax + BitVec.ofNat 64 64, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, h1, -, hg, hf, hr, hw⟩ := stores_ok (fun i => [unpckh (q (2 * i)) (q (2 * i + 1)),
      .movdquStore (Impl.Aes.X86_64.at_ kp (64 + 16 * i)) (q (2 * i))]) (fun s => s.gpr .rax + BitVec.ofNat 64 64) 1
    (fun i hi s h => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
      obtain ⟨s', e, hm, hx, hg, hr, hw⟩ := highStep (q (2 * i)) (q (2 * i + 1)) i s h
      refine ⟨s', _, e, by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hm, fun j hj => by
        rw [qword_unpckh _ _ hj]; rfl, fun j hj hne => hx _ fun h => ?_, hg, hr, hw⟩
      have := q_inj hj (by omega) h
      omega)
    (fun s s' h => by simp only [h]) s (fun i hi => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hin i hi) 4
    (Nat.le_refl _)
  exact ⟨s', e, h1, hg, hf, hr, hw⟩

/-! ## A pair of keys -/

/-- The invariant of the key loop: `n` keys stored, the source at `r10`. -/
structure KS (s₀ : State) (b sch : Addr) (nr : Nat) (n : Nat) (cnt : BitVec 64) (s : State) : Prop where
  env : Env0 s
  r9 : s.gpr .r9 = b
  rax : s.gpr .rax = keyAddr b n
  r10 : s.gpr .r10 = sch + BitVec.ofNat 64 (16 * n)
  rdi : s.gpr .rdi = cnt
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b, 1480⟩] s₀.mem s.mem
  keys : ∀ i < n, KeyAt s.mem (keyAddr b i) (i % 2 == 1)
    (Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i)

/-- What the key setup needs. -/
structure KPre (b sch : Addr) (nr : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = b
  rdi : s.gpr .rdi = sch
  rsi : s.gpr .rsi = BitVec.ofNat 64 nr
  nrs : nr = 10 ∨ nr = 12 ∨ nr = 14
  sc : ⟨b, 2048⟩ ∈ s.wr ∨ ⟨b, 1480⟩ ∈ s.wr
  schIn : ⟨sch, 240⟩ ∈ s.rd
  disj : Region.Disjoint ⟨sch, 240⟩ ⟨b, 1480⟩

theorem KeyAt.frame {m m' : Mem} {a : Addr} {f : Bool} {rk : List Byte} (h : KeyAt m a f rk) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 64⟩ r) : KeyAt m' a f rk :=
  h.congrW fun j hj => (hf.readW (r := ⟨a, 64⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)).symm

/-- The machine after a store of keys. -/
theorem Env0.store {s s' : State} (he : Env0 s) (hg : s'.gpr = s.gpr) (hw : s'.wr = s.wr) {R : Region}
    (hf : Frame [R] s.mem s'.mem) (hd : Region.Disjoint ⟨s.gpr .r9 + BitVec.ofNat 64 144, 144⟩ R) : Env0 s' where
  ok := he.ok.congr (by rw [hg]) hw
  masks m hm l hl := by
    have h1 := mask_ge m hm
    have h2 := mask_slots m hm
    rw [hg, hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 144, 144⟩) (Offset.contains _ (by omega) (by omega) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact he.masks m hm l hl

theorem keyAddr_disj (b : Addr) {i n len : Nat} (h : i < n) (hn : 64 * n + len ≤ 1064) :
    Region.Disjoint ⟨keyAddr b i, 64⟩ ⟨keyAddr b n, len⟩ :=
  Offset.disjoint _ (.inl (by omega)) (by simp only [keysOff]; omega) (by simp only [keysOff]; omega)

theorem mask_disj (b : Addr) {n len : Nat} (hn : 64 * n + len ≤ 1064) :
    Region.Disjoint ⟨b + BitVec.ofNat 64 144, 144⟩ ⟨keyAddr b n, len⟩ :=
  Offset.disjoint _ (.inl (by simp only [keysOff]; omega)) (by decide) (by simp only [keysOff]; omega)

theorem sub_scratch (b : Addr) {d len : Nat} (h : d + len ≤ 1480) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, len⟩ ⟨b, 1480⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
  have := (x - b).isLt
  omega

variable {s₀ : State} {b sch : Addr} {nr : Nat}

theorem KS.src {n : Nat} {cnt : BitVec 64} {s : State} (hp : KPre b sch nr s₀) (h : KS s₀ b sch nr n cnt s) {i : Nat}
    (hi : i ≤ nr) {d : Nat} (hd : d + 8 ≤ 16) :
    s.mem.readW (sch + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (sch + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 d) 64 := by
  have := hp.nrs
  refine h.frame.readW (r := ⟨sch, 240⟩) ?_ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.disj) (by decide)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem KPre.inSch (hp : KPre b sch nr s₀) {s : State} (hr : s.rd = s₀.rd) {i : Nat} (hi : i ≤ nr) :
    InRegions (s.rd ++ s.wr) (sch + BitVec.ofNat 64 (16 * i)) 16 := by
  have := hp.nrs
  exact ⟨_, List.mem_append_left _ (by rw [hr]; exact hp.schIn), Offset.contains_base _ (by omega) (by omega)⟩

theorem KPre.inScr (hp : KPre b sch nr s₀) {s : State} (hw : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 1480) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n := by
  rw [hw]
  rcases hp.sc with h | h
  · exact ⟨_, h, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨_, h, Offset.contains_base _ hd (by omega)⟩

/-- From the halves in the registers, the slices: of key `i 0` in form 0 in the low
quadwords, of key `i 1` in form 1 in the high ones. -/
theorem keyBs_ok (w : List Byte) (i : Nat → Nat) {s : State} (he : Env0 s)
    (hq : ∀ l < 2, ∀ n < 16, ∀ j < 8,
      (qword (s.xmm (q (4 * (n / 8)))) l).getLsbD (8 * (n % 8) + j) = ((rkState (Spec.Aes.roundKey w (i l))).getD n 0).getLsbD j) :
    ∃ s', runBlock isa keyBs s = some s' ∧ Keep s s' ∧
      ∀ l < 2, BsRel 4 (l == 1) (lane q s' l) fun _ => rkState (Spec.Aes.roundKey w (i l)) := by
  obtain ⟨s1, e1, k1, h1⟩ := layer_ok keyMid_check (by decide +kernel) (by decide) he
  obtain ⟨s2, e2, h2, g2, m2, r2, w2⟩ := pick_ok s1
  have k2 := keep_of k1.env g2 m2 r2 w2
  obtain ⟨s3, e3, k3, h3⟩ := layer_ok keyOut_check (by decide +kernel) (by decide) k2.env
  refine ⟨s3, ?_, k1.trans (k2.trans k3), fun l hl j hj n hn k hk => ?_⟩
  · rw [keyBs, Interleave.runBlock_append, Interleave.runBlock_append, e1, Option.bind_some, e2, Option.bind_some, e3]
  have hp : posAt 4 (l == 1) n k < 64 := Nat.lt_of_lt_of_le (posAt_lt _ hn hk) (by decide)
  have hp' : posAt 4 (l == 1) n (j % 4) < 64 := Nat.lt_of_lt_of_le (posAt_lt _ hn (by omega)) (by decide)
  have e : posAt 4 (l == 1) n k - posAt 4 (l == 1) n k % 4 + j % 4 = posAt 4 (l == 1) n (j % 4) := by
    rw [posAt_mod _ n hk]; simp only [posAt]; omega
  rw [h3 l hl j hj _ hp]
  simp only [keyOutT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, e]
  rw [h2 l hl _ (by omega), h1 l hl _ (by omega) _ hp']
  have hm : keyMidT (4 * (j / 4) + l) (posAt 4 (l == 1) n (j % 4)) = midT (l == 1) (j / 4) (posAt 4 (l == 1) n (j % 4)) := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [keyMidT, show (4 * (j / 4) + 0) % 4 = 0 by omega, ite_true, show (4 * (j / 4) + 0) / 4 = j / 4 by omega]; rfl
    · simp only [keyMidT, show (4 * (j / 4) + 1) % 4 = 1 by omega, Nat.one_ne_zero, ite_false, ite_true,
        show (4 * (j / 4) + 1) / 4 = j / 4 by omega]; rfl
  rw [hm]
  simp only [midT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_posAt _ hn (show j % 4 < 4 by omega),
    posAt_mod _ n (show j % 4 < 4 by omega), show 4 * (j / 4) + j % 4 = j by omega]
  exact hq l hl n hn j hj

/-- The slices of a lane, stored. -/
theorem keyAt_of {s : State} {f : Bool} {rk : List Byte} {l : Nat}
    (h : BsRel 4 f (lane q s l) fun _ => rkState rk) {m : Mem} {a : Addr}
    (hm : ∀ j < 8, m.readW (a + BitVec.ofNat 64 (8 * j)) 64 = lane q s l j) : KeyAt m a f rk :=
  h.congrW fun j hj => (hm j hj).symm

theorem low_sub (b : Addr) : ∀ r ∈ [(⟨b, 288⟩ : Region)], ∃ r' ∈ [(⟨b, 1480⟩ : Region)], Region.Sub r r' := fun r hr => by
  rw [List.mem_singleton.mp hr]
  exact ⟨_, List.mem_singleton.mpr rfl, fun x hx => by simp only [Region.Contains] at hx ⊢; omega⟩

theorem key_low_disj (b : Addr) {i : Nat} (hi : i ≤ 14) : ∀ r ∈ [(⟨b, 288⟩ : Region)], Region.Disjoint ⟨keyAddr b i, 64⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by simp only [keysOff]; omega) (by simp only [keysOff]; omega)

theorem keyBody_ok (hp : KPre b sch nr s₀) {n c : Nat} (hn : n + 2 ≤ nr) (h2 : n % 2 = 0) (hc : c < 2 ^ 32) {s : State}
    (h : KS s₀ b sch nr n (BitVec.ofNat 64 (c + 1)) s) :
    WP isa (.block keyBody) s fun s' => KS s₀ b sch nr (n + 2) (BitVec.ofNat 64 c) s' ∧
      X86_64.eval .ne s' = some (decide (c ≠ 0)) := by
  have hnr := hp.nrs
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1)) := ⟨_, rfl⟩
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  obtain ⟨s1, e1, q1, g1, m1, r1, w1⟩ := load2_ok s (by rw [h.r10]; exact hp.inSch h.rd (by omega))
    (by rw [h.r10, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * n + 16 = 16 * (n + 1) by omega]
        exact hp.inSch h.rd (by omega))
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2s⟩ := keyBs_ok w (fun l => n + l) k1.env fun l hl x hx j hj => by
    rw [q1 l hl _ (by omega), h.r10, BitVec.add_assoc sch, ← BitVec.ofNat_add, show 16 * n + 16 * l = 16 * (n + l) by omega,
      h.src hp (by omega) (by omega), hw]
    exact key_bit _ _ (by omega) hx hj
  have k2' := k1.trans k2
  have rax2 : s2.gpr .rax = keyAddr b n := by rw [k2'.gpr, h.rax]
  have r92 : s2.gpr .r9 = b := by rw [k2'.gpr, h.r9]
  have wr2 : s2.wr = s₀.wr := k2'.wr.trans h.wr
  obtain ⟨s3, e3, q3, x3, g3, f3, r3, w3⟩ := storeLow_ok s2 (fun i hi => by
    rw [rax2, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr2 (by simp only [keysOff]; omega))
  rw [rax2] at q3 f3
  have he3 := k2.env.store g3 w3 f3 (by rw [r92]; exact mask_disj b (by omega))
  have h3s : BsRel 4 true (lane q s3 1) fun _ => rkState (Spec.Aes.roundKey w (n + 1)) :=
    (h2s 1 (by decide)).congrW fun j hj => by rw [lane, lane, x3 j hj]
  have g4 : s3.gpr = s.gpr := g3.trans k2'.gpr
  have wr4 : s3.wr = s₀.wr := w3.trans wr2
  obtain ⟨s5, e5, q5, g5, f5, r5, w5⟩ := storeHigh_ok s3 (fun i hi => by
    rw [g4, h.rax, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr4 (by simp only [keysOff]; omega))
  have e64 : keyAddr b n + BitVec.ofNat 64 64 = keyAddr b (n + 1) := by
    rw [keyAddr, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show keysOff + 64 * (n + 1) = keysOff + 64 * n + 64 by omega]
  rw [g4, h.rax, e64] at q5 f5
  have he5 := he3.store g5 w5 f5 (by rw [g4, h.r9]; exact mask_disj b (by omega))
  have f2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2'.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  have hfr : Frame [⟨b, 1480⟩] s.mem s5.mem := by
    refine ((f2.sub (low_sub b)).trans (f3.sub fun r hr => ?_)).trans (f5.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  have keys : ∀ i < n + 2, KeyAt s5.mem (keyAddr b i) (i % 2 == 1) (Spec.Aes.roundKey w i) := by
    intro i hi
    by_cases hi1 : i = n + 1
    · subst hi1
      rw [show ((n + 1) % 2 == 1) = true by simp; omega]
      exact keyAt_of (l := 1) h3s q5
    have hd : KeyAt s3.mem (keyAddr b i) (i % 2 == 1) (Spec.Aes.roundKey w i) := by
      by_cases hi0 : i = n
      · subst hi0
        rw [show (i % 2 == 1) = false by simp; omega]
        exact keyAt_of (l := 0) (h2s 0 (by decide)) q3
      · refine KeyAt.frame (KeyAt.frame ?_ f2 (key_low_disj b (by omega))) f3 fun r hr => ?_
        · rw [hw]; exact h.keys i (by omega)
        · rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)
    exact hd.frame f5 fun r hr => by rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)
  refine WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3,
    WP.of_runBlock ⟨s5, e5, ?_⟩⟩⟩⟩
  have g5' : s5.gpr = s.gpr := g5.trans g4
  have rd5 : s5.rd = s₀.rd := r5.trans (r3.trans (k2'.rd.trans h.rd))
  have wr5 : s5.wr = s₀.wr := w5.trans wr4
  have ecnt : s5.gpr .rdi - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
    rw [g5', h.rdi, show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
    show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨he5.ok.congr (by simp [gpr_setReg, gpr_arithFlags, cfg]) rfl, ?_⟩, ?_, ?_, ?_, ?_, fun x a c d => ?_, rd5, wr5,
    h.frame.trans hfr, fun i hi => ?_⟩, ?_⟩
  · intro m hm l hl
    simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, mem_setReg, mem_arithFlags]
    exact he5.masks m hm l hl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, g5', h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g5', h.rax]
    rw [keyAddr, keyAddr, BitVec.add_assoc, show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide,
      ← BitVec.ofNat_add, show keysOff + 64 * (n + 2) = keysOff + 64 * n + 128 by omega]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g5', h.r10]
    rw [BitVec.add_assoc, show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, ← BitVec.ofNat_add]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false, g5']; exact h.gpr x a c d
  · rw [← hw]; exact keys i hi
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

/-- The last key. -/
theorem lastKey_ok (hp : KPre b sch nr s₀) {s : State} (h : KS s₀ b sch nr nr 0 s) :
    WP isa (.block (keyLoad1 ++ keyBs ++ storeLow)) s fun s' => Env0 s' ∧
      (∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s₀.gpr x) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [⟨b, 1480⟩] s₀.mem s'.mem ∧
      ∀ i ≤ nr, KeyAt s'.mem (keyAddr b i) (i % 2 == 1)
        (Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i) := by
  have hnr := hp.nrs
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1)) := ⟨_, rfl⟩
  obtain ⟨s1, e1, q1, g1, m1, r1, w1⟩ := load1_ok s (by rw [h.r10]; exact hp.inSch h.rd (Nat.le_refl _))
  have k1 := keep_of h.env g1 m1 r1 w1
  obtain ⟨s2, e2, k2, h2s⟩ := keyBs_ok w (fun _ => nr) k1.env fun l hl x hx j hj => by
    rw [q1 l hl _ (by omega), h.r10, h.src hp (Nat.le_refl _) (by omega), hw]
    exact key_bit _ _ (Nat.le_refl _) hx hj
  have k2' := k1.trans k2
  have rax2 : s2.gpr .rax = keyAddr b nr := by rw [k2'.gpr, h.rax]
  have r92 : s2.gpr .r9 = b := by rw [k2'.gpr, h.r9]
  have wr2 : s2.wr = s₀.wr := k2'.wr.trans h.wr
  obtain ⟨s3, e3, q3, x3, g3, f3, r3, w3⟩ := storeLow_ok s2 (fun i hi => by
    rw [rax2, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr wr2 (by simp only [keysOff]; omega))
  rw [rax2] at q3 f3
  have he3 := k2.env.store g3 w3 f3 (by rw [r92]; exact mask_disj b (by omega))
  have f2 : Frame [⟨b, 288⟩] s.mem s2.mem := by
    have := k2'.frame
    rwa [slotRegion, show s.gpr cfg.base = b from h.r9] at this
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, he3,
    fun x a c d => by rw [g3, k2'.gpr, h.gpr x a c d], r3.trans (k2'.rd.trans h.rd), w3.trans wr2,
    h.frame.trans ((f2.sub (low_sub b)).trans (f3.sub fun r hr => ?_)), fun i hi => ?_⟩⟩⟩))
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  · rw [← hw]
    by_cases hi0 : i = nr
    · subst hi0
      rw [show (i % 2 == 1) = false by simp; omega]
      exact keyAt_of (l := 0) (h2s 0 (by decide)) q3
    · refine KeyAt.frame (KeyAt.frame ?_ f2 (key_low_disj b (by omega))) f3 fun r hr => ?_
      · rw [hw]; exact h.keys i (by omega)
      · rw [List.mem_singleton.mp hr]; exact keyAddr_disj b (by omega) (by omega)

/-! ## The constant -/

theorem flip_ok (j : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (flip j) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 (8 * j))
        (~~~ s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 64) ∧
      (∀ x, x ≠ .r10 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 (8 * j)) 8 := by
    obtain ⟨R, hR, hc⟩ := hin
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have e : BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 64 := by decide
  simp only [Impl.Aes.X86_64.Sse.flip, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load64,
    State.store64, ea_at, show kp = Reg.rax from rfl, hin', ite_true, Option.map_some, Option.bind_some, e, gpr_setReg,
    gpr_arithFlags, reduceCtorEq, ite_false, hin, wr_setReg, wr_arithFlags, mem_setReg, mem_arithFlags, Option.some.injEq,
    exists_eq_left', BitVec.xor_allOnes]
  refine ⟨trivial, fun x c => ?_, by first | rfl | trivial, by first | rfl | trivial⟩
  simp only [c, ite_false]

theorem flips_ok (l : List Nat) (hn : l.Nodup) (hl : ∀ j ∈ l, j < 8) (s : State) (a : Addr) (ha : s.gpr .rax = a)
    (hin : ∀ j < 8, InRegions s.wr (a + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (l.flatMap Impl.Aes.X86_64.Sse.flip) s = some s' ∧
      (∀ j < 8, s'.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64 =
        if j ∈ l then ~~~ s.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64 else s.mem.readW (a + BitVec.ofNat 64 (8 * j)) 64) ∧
      (∀ x, x ≠ .r10 → s'.gpr x = s.gpr x) ∧ Frame [⟨a, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl, fun _ _ => by simp, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  | cons m l ih =>
    obtain ⟨hm, hn'⟩ := List.nodup_cons.mp hn
    have hm8 := hl m List.mem_cons_self
    obtain ⟨s1, e1, m1, g1, r1, w1⟩ := flip_ok m s (by rw [ha]; exact hin m hm8)
    obtain ⟨s2, e2, q2, g2, f2, r2, w2⟩ := ih hn' (fun j hj => hl j (List.mem_cons_of_mem _ hj)) s1
      ((g1 _ (by decide)).trans ha) (by rw [w1]; exact hin)
    rw [ha] at m1
    refine ⟨s2, by rw [List.flatMap_cons, Interleave.runBlock_append, e1, Option.bind_some, e2], fun j hj => ?_,
      fun x c => (g2 x c).trans (g1 x c), ?_, r2.trans r1, w2.trans w1⟩
    · rw [q2 j hj, m1]
      by_cases hjm : j = m
      · subst hjm
        simp only [hm, ite_false, List.mem_cons_self, ite_true]
        exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        simp only [List.mem_cons, hjm, false_or]
    · rw [m1] at f2
      exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))).trans f2

theorem complement_eq : complement = [0, 1, 5, 6].flatMap Impl.Aes.X86_64.Sse.flip ++
    ([.alu .add kp (.imm 64), .alu .sub .rdi (.imm 1)] : List Instr) := by decide

/-- A key with the slices flipped is the key with `{63}` added. -/
theorem keyAt_flip {m m' : Mem} {a : Addr} {f : Bool} {rk : List Byte} (hr : rk.length = 16) (h : KeyAt m a f rk)
    (hm : ∀ j < 8, m'.readW (a + BitVec.ofNat 64 (8 * j)) 64 =
      if j ∈ [0, 1, 5, 6] then ~~~ m.readW (a + BitVec.ofNat 64 (8 * j)) 64 else m.readW (a + BitVec.ofNat 64 (8 * j)) 64) :
    KeyAt m' a f (rk63 rk) := fun j hj n hn k hk => by
  have hb := h j hj n hn k hk
  have hp : posAt 4 f n k < 64 := Nat.lt_of_lt_of_le (posAt_lt f hn hk) (by decide)
  dsimp only at hb ⊢
  rw [getD_rkState _ hn] at hb ⊢
  rw [hm j hj, getD_rk63 _ (by omega), BitVec.getLsbD_xor, ← hb]
  have : ∀ j < 8, (j ∈ [0, 1, 5, 6]) = ((0x63 : Byte).getLsbD j = true) := by decide
  simp only [this j hj]
  split
  · rename_i h1; rw [h1]; simp [hp]
  · rename_i h1; simp only [Bool.not_eq_true] at h1; rw [h1]; simp

/-- The invariant of the complementing loop: keys `1 … m` done. -/
structure CS (s₀ : State) (b sch : Addr) (nr : Nat) (m : Nat) (s : State) : Prop where
  env : Env0 s
  rax : s.gpr .rax = keyAddr b (m + 1)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (nr - m)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b, 1480⟩] s₀.mem s.mem
  keys : ∀ i ≤ nr, KeyAt s.mem (keyAddr b i) (i % 2 == 1)
    (if i ≤ m then kr (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i
      else Spec.Aes.roundKey (Spec.Aes.bytesAt s₀.mem sch (16 * (nr + 1))) i)

theorem complement_ok (hp : KPre b sch nr s₀) {m : Nat} (hm : m < nr) {s : State} (h : CS s₀ b sch nr m s) :
    WP isa (.block complement) s fun s' => CS s₀ b sch nr (m + 1) s' ∧
      X86_64.eval .ne s' = some (decide (nr - (m + 1) ≠ 0)) := by
  have hnr := hp.nrs
  have h9 : s.gpr .r9 = b := by rw [h.gpr _ (by decide) (by decide) (by decide), hp.r9]
  rw [complement_eq]
  obtain ⟨s1, e1, q1, g1, f1, r1, w1⟩ := flips_ok [0, 1, 5, 6] (by decide) (by decide) s _ h.rax fun j hj => by
    rw [keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.inScr h.wr (by simp only [keysOff]; omega)
  refine WP.block_append (WP.of_runBlock ⟨s1, e1, ?_⟩)
  have h91 : s1.gpr .r9 = b := (g1 _ (by decide)).trans h9
  have hmask : ∀ k ∈ maskVals, ∀ l < 2, qword (s1.mem.readW (xAddr b k.1) 128) l = k.2 := fun k hk l hl => by
    have a1 := mask_ge k hk
    have a2 := mask_slots k hk
    rw [f1.readW (r := ⟨b + BitVec.ofNat 64 144, 144⟩) (Offset.contains _ (by omega) (by omega) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact mask_disj b (by omega)) (by decide)]
    have := h.env.masks k hk l hl
    rwa [h9] at this
  have ecnt : s1.gpr .rdi - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nr - (m + 1)) := by
    rw [g1 _ (by decide), h.rdi, show nr - m = nr - (m + 1) + 1 by omega,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
    show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨fun k hk => ?_, by decide⟩, fun k hk l hl => ?_⟩, ?_, ?_, fun x a c d => ?_, r1.trans h.rd, w1.trans h.wr,
    h.frame.trans (f1.sub fun r hr => ?_), fun i hi => ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, cfg, h91, wr_setReg, wr_arithFlags]
    exact hp.inScr (w1.trans h.wr) (by simp only [cfg] at hk; omega)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, mem_setReg, mem_arithFlags, h91]
    exact hmask k hk l hl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g1 _ (show Reg.rax ≠ .r10 by decide), h.rax]
    rw [keyAddr, keyAddr, BitVec.add_assoc, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide,
      ← BitVec.ofNat_add, show keysOff + 64 * (m + 1 + 1) = keysOff + 64 * (m + 1) + 64 by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, d, ite_false, g1 x c]; exact h.gpr x a c d
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton.mpr rfl, sub_scratch b (by simp only [keysOff]; omega)⟩
  · simp only [mem_setReg, mem_arithFlags]
    by_cases hi1 : i = m + 1
    · subst hi1
      simp only [Nat.le_refl, ite_true, kr, Nat.succ_ne_zero, ite_false]
      have := h.keys (m + 1) hi
      rw [ite_eq_right (by omega)] at this
      exact keyAt_flip (rk_length _ _ hi) this q1
    · have := h.keys i hi
      simp only [show (i ≤ m + 1) = (i ≤ m) by apply propext; omega]
      exact this.frame f1 fun r hr => by
        rw [List.mem_singleton.mp hr]
        rcases Nat.lt_or_gt_of_ne hi1 with hlt | hgt
        · exact keyAddr_disj b hlt (by omega)
        · exact (keyAddr_disj b hgt (by omega)).symm
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem shr1 : ∀ n, n = 10 ∨ n = 12 ∨ n = 14 → (BitVec.ofNat 64 n >>> (1 : Nat) : BitVec 64) = BitVec.ofNat 64 (n / 2) := by
  rintro n (rfl | rfl | rfl) <;> decide

/-- What the key setup leaves. -/
structure KPost (b sch : Addr) (nr : Nat) (s s' : State) : Prop where
  ready : Ready b nr (Spec.Aes.bytesAt s.mem sch (16 * (nr + 1))) s'.mem s'.rd s'.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b, 1480⟩] s.mem s'.mem

theorem keys_ok (hp : KPre b sch nr s₀) : WP isa keys s₀ (KPost b sch nr s₀) := by
  have hnr := hp.nrs
  -- the masks and the pointers
  obtain ⟨s1, e1, a1, -, f1, g1, r1, w1⟩ := masks_list maskVals (by decide) mask_slots s₀ fun k hk => by
    rw [hp.r9, xAddr]; exact hp.inScr rfl (by omega)
  rw [hp.r9] at a1 f1
  have g9 : s1.gpr .r9 = b := (g1 _ (by decide)).trans hp.r9
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s1, by rw [setMasks_eq]; exact e1, ?_⟩))
  refine WP.mono (Q := KS s₀ b sch nr 0 (BitVec.ofNat 64 (nr / 2))) ?_ fun s2 h2 => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execShift, readSrc, Option.bind_some,
      Option.map_some, show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false,
      Nat.le_refl, Nat.reduceLeDiff, and_self, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨fun k hk => ?_, by decide⟩, ?_⟩, ?_, ?_, ?_, ?_, fun x a c d => ?_, r1, w1, f1.sub (low_sub b), fun i hi =>
      absurd hi (Nat.not_lt_zero _)⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, cfg, g9]
      exact hp.inScr w1 (by simp only [cfg] at hk; omega)
    · intro k hk l hl
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, g9]
      exact a1 k hk l hl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, g9]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true, g9]
      exact (keyAddr_zero b).symm
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false, ite_true, g1 _ (show Reg.rdi ≠ .rax by decide),
        hp.rdi]
      simp
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, g1 _ (show Reg.rsi ≠ .rax by decide), hp.rsi]
      exact shr1 nr hnr
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, c, d, ite_false, g1 x a]
  -- the pairs
  refine WP.seq (WP.mono (Q := KS s₀ b sch nr nr 0) ?_ fun s3 h3 => ?_)
  · let I : Nat → State → Prop := fun c s => ∃ m, c = nr / 2 - m ∧ m < nr / 2 ∧
      KS s₀ b sch nr (2 * m) (BitVec.ofNat 64 (nr / 2 - m)) s
    refine WP.loop (M := isa) I ?_ (nr / 2) s2 ⟨0, rfl, by omega, h2⟩
    rintro c s' ⟨m, rfl, hm, hs'⟩
    rw [show nr / 2 - m = nr / 2 - (m + 1) + 1 by omega] at hs'
    refine WP.mono (keyBody_ok hp (by omega) (by omega) (by omega) hs') fun s4 ⟨h4, hz⟩ => ?_
    by_cases hl : nr / 2 - (m + 1) = 0
    · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
      rw [hl, show 2 * m + 2 = nr by omega] at h4
      exact h4
    · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h4⟩
  -- the last key
  refine WP.seq (WP.block_append (WP.mono (lastKey_ok hp h3) fun s4 ⟨he4, g4, rd4, wr4, fr4, k4⟩ => ?_))
  have g49 : s4.gpr .r9 = b := (g4 _ (by decide) (by decide) (by decide)).trans hp.r9
  have e64 : BitVec.signExtend 64 (BitVec.ofNat 32 (keysOff + 64)) = BitVec.ofNat 64 (keysOff + 64 * (0 + 1)) := by decide
  refine WP.mono (Q := CS s₀ b sch nr 0) ?_ fun s5 h5 => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
      Option.map_some, show kp = Reg.rax from rfl, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨fun k hk => ?_, by decide⟩, ?_⟩, ?_, ?_, fun x a c d => ?_, rd4, wr4, fr4, fun i hi => ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, cfg, g49]
      exact hp.inScr wr4 (by simp only [cfg] at hk; omega)
    · intro k hk l hl
      simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, g49]
      have := he4.masks k hk l hl
      rwa [g49] at this
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, g49]
      rw [e64]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, g4 _ (show Reg.rsi ≠ .rax by decide) (by decide) (by decide), hp.rsi]
      rfl
    · simp only [gpr_setReg, gpr_arithFlags, a, d, ite_false, g4 x a c d]
    · have := k4 i hi
      by_cases h0 : i = 0
      · subst h0; simpa [kr, mem_setReg, mem_arithFlags] using this
      · simpa [h0, mem_setReg, mem_arithFlags] using this
  -- the constant
  let I : Nat → State → Prop := fun c s => ∃ m, c = nr - m ∧ m < nr ∧ CS s₀ b sch nr m s
  refine WP.loop (M := isa) I ?_ nr s5 ⟨0, rfl, by omega, h5⟩
  rintro c s' ⟨m, rfl, hm, hs'⟩
  refine WP.mono (complement_ok hp hm hs') fun s6 ⟨h6, hz⟩ => ?_
  by_cases hl : nr - (m + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    have g9' : s6.gpr .r9 = b := (h6.gpr _ (by decide) (by decide) (by decide)).trans hp.r9
    refine ⟨⟨by rw [h6.wr]; exact hp.sc, fun i hi => ?_, ?_, hnr, fun i hi => rk_length _ _ hi⟩, h6.gpr, h6.rd, h6.wr, h6.frame⟩
    · have := h6.keys i hi
      rwa [ite_eq_left (by omega)] at this
    · have := h6.env.masks
      rwa [g9'] at this
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, m + 1, rfl, by omega, h6⟩

end VG.Proof.Aes.X86_64.Sse

end

section

/-! # Blocks in and out of the buffer -/

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Proof.Aes.Memory (Processed)

/-! ## Bytes -/

theorem writeW128 (m : Mem) (a : Addr) (v : BitVec 128) : m.writeW a v = m.write a 16 v := by
  rw [Mem.writeW]; simp

theorem readW128_byte (m : Mem) (a : Addr) {n : Nat} (hn : n < 16) :
    (m.readW a 128).extractLsb' (8 * n) 8 = m (a + BitVec.ofNat 64 n) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hn]
  simp only [Mem.readW]
  rfl

theorem writeW128_byte (m : Mem) (a : Addr) (v : BitVec 128) {n : Nat} (hn : n < 16) :
    (m.writeW a v) (a + BitVec.ofNat 64 n) = v.extractLsb' (8 * n) 8 := by
  rw [writeW128, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hn]

/-- The blocks of the buffer. -/
def bufS (m : Mem) (b : Addr) (i : Nat) : Spec.Aes.State := Spec.Aes.stateAt m (bufAddr b i)

theorem bufIs_bufS (m : Mem) (b : Addr) : BufIs m b (bufS m b) := fun i _ n hn => by
  rw [bufS, Spec.Aes.stateAt, getD_ofFn _ hn]

/-! ## The size of a batch -/

theorem batchSize_ok {s : State} {r : Nat} (hr : r < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 r) :
    WP isa (.block batchSize) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (min 8 r) ∧ s'.gpr .r10 = BitVec.ofNat 64 (min 8 r) ∧
      s'.gpr .rax = bufAddr (s.gpr .r9) 0 ∧
      (∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hlt : ((s.gpr .r8).toNat < (8 : BitVec 64).toNat) = (r < 8) := by
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]; rfl
  have e0 : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * bufSlot 0)) = BitVec.ofNat 64 (16 * bufSlot 0) := by decide
  by_cases h : r < 8
  · simp only [batchSize, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execCmov, readSrc, e8,
      Option.map_some, Option.bind_some, gpr_setReg, reduceCtorEq, ite_false, arithFlags, State.setFlags, X86_64.eval,
      hlt, h, decide_true, ite_true, Option.some.injEq, exists_eq_left', e0]
    refine ⟨?_, ?_, ?_, fun x a c d => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [h8, Nat.min_eq_right (Nat.le_of_lt h)]
    · simp only [h8, Nat.min_eq_right (Nat.le_of_lt h)]
    · rfl
    · simp only [a, c, d, ite_false]
  · simp only [batchSize, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execCmov, readSrc, e8,
      Option.map_some, Option.bind_some, gpr_setReg, reduceCtorEq, ite_false, arithFlags, State.setFlags, X86_64.eval,
      hlt, h, decide_false, ite_true, Option.some.injEq, exists_eq_left', e0, Bool.false_eq_true]
    refine ⟨?_, ?_, ?_, fun x a c d => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [Nat.min_eq_left (Nat.le_of_not_lt h)]; rfl
    · simp only [Nat.min_eq_left (Nat.le_of_not_lt h)]; rfl
    · rfl
    · simp only [a, c, d, ite_false]

theorem add00 (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem addNat (a : BitVec 64) (x k : Nat) (h : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k) :
    a + BitVec.ofNat 64 x + BitVec.signExtend 64 (BitVec.ofNat 32 k) = a + BitVec.ofNat 64 (x + k) := by
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem subOne (c : Nat) : BitVec.ofNat 64 (c + 1) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-! ## Into the buffer -/

/-- After `j` blocks from `p` (`s₁`: before the loop). -/
structure CI (s₁ : State) (b p : Addr) (t j : Nat) (s : State) : Prop where
  r11 : s.gpr .r11 = p + BitVec.ofNat 64 (16 * j)
  rax : s.gpr .rax = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (t - j)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .r11 → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [bufR b] s₁.mem s.mem
  buf : ∀ i < j, ∀ n < 16, s.mem (bufAddr b i + BitVec.ofNat 64 n) = s₁.mem (p + BitVec.ofNat 64 (16 * i + n))

theorem bufAddr_eq (b : Addr) (j : Nat) : bufAddr b j = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j) := by
  rw [bufAddr, show 16 * bufSlot j = 16 * bufSlot 0 + 16 * j by simp only [bufSlot]; omega]

theorem copyIn_ok {s₁ : State} {b p : Addr} {t : Nat} (ht : t ≤ 8)
    (hsrc : ∀ i < t, InRegions (s₁.rd ++ s₁.wr) (p + BitVec.ofNat 64 (16 * i)) 16)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16)
    (hd : ∀ i < t, Region.Disjoint ⟨p + BitVec.ofNat 64 (16 * i), 16⟩ (bufR b)) {j : Nat} (hj : j < t) {s : State}
    (h : CI s₁ b p t j s) :
    WP isa (.block copyIn) s fun s' => CI s₁ b p t (j + 1) s' ∧ X86_64.eval .ne s' = some (decide (t - (j + 1) ≠ 0)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 0) 16 := by
    rw [h.r11, h.rd, h.wr]; simpa using hsrc j hj
  have hout : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 0) 16 := by
    rw [h.rax, h.wr, ← bufAddr_eq]; simpa using hbuf j (by omega)
  have ecnt : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (t - (j + 1)) := by
    rw [h.r10, show t - j = t - (j + 1) + 1 by omega, subOne]
  apply WP.of_runBlock
  simp only [copyIn, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load128,
    State.store128, ea_at, hin, hout, ite_true, Option.map_some, Option.bind_some, gpr_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm,
    gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  have hfw : Frame [bufR b] s.mem (s.mem.writeW (bufAddr b j) (s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (buf_contains b (by omega))
  refine ⟨⟨?_, ?_, ?_, fun x a c d => ?_, h.rd, h.wr, ?_, fun i hi n hn => ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.r11]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rax]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false]; exact h.gpr x a c d
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.r11, add00, ← bufAddr_eq]
    exact h.frame.trans hfw
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.r11, add00, ← bufAddr_eq]
    by_cases hij : i = j
    · subst hij
      rw [writeW128_byte _ _ _ hn, readW128_byte _ _ hn, BitVec.add_assoc, ← BitVec.ofNat_add]
      have := h.frame.bytes (R := ⟨p + BitVec.ofNat 64 (16 * i), 16⟩)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd i hj) (show (16 : Nat) ≤ 2 ^ 64 by decide) hn
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at this
    · rw [← h.buf i (by omega) n hn]
      have := (Frame.refl [⟨bufAddr b j, 16⟩] s.mem).writeW List.mem_cons_self
        (s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128) (Region.contains_self _ _)
      refine this.bytes (R := ⟨bufAddr b i, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hn
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := 16 * bufSlot i) (n := 16) (e := 16 * bufSlot j) (k := 16) (by simp only [bufSlot]; omega)
        (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem copyIn_loop {s₁ : State} {b p : Addr} {t : Nat} (ht : t ≤ 8) (h0 : 0 < t)
    (hsrc : ∀ i < t, InRegions (s₁.rd ++ s₁.wr) (p + BitVec.ofNat 64 (16 * i)) 16)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16)
    (hd : ∀ i < t, Region.Disjoint ⟨p + BitVec.ofNat 64 (16 * i), 16⟩ (bufR b)) {s : State} (h : CI s₁ b p t 0 s) :
    WP isa (.loop (.block copyIn) .ne) s (CI s₁ b p t t) := by
  let I : Nat → State → Prop := fun c s => ∃ j, c = t - j ∧ j < t ∧ CI s₁ b p t j s
  refine WP.loop (M := isa) I ?_ t s ⟨0, rfl, h0, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (copyIn_ok ht hsrc hbuf hd hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : t - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = t by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

/-! ## Out of the buffer -/

/-- After `j` blocks of the batch that starts at block `k` (`s₁`: before the loop). -/
structure CO (s₁ : State) (m₀ : Mem) (b D : Addr) (n k t : Nat) (F : Nat → Spec.Aes.State) (j : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = D + BitVec.ofNat 64 (16 * (k + j))
  rax : s.gpr .rax = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (t - j)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨D, 16 * n⟩] s₁.mem s.mem
  done : Processed m₀ s.mem D n (k + j) F

theorem copyOut_ok {s₁ : State} {m₀ : Mem} {b D : Addr} {n k t : Nat} {F : Nat → Spec.Aes.State} (ht : t ≤ 8)
    (hkt : k + t ≤ n) (hn : 16 * n ≤ 2 ^ 64) (hD : ⟨D, 16 * n⟩ ∈ s₁.wr)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16) (hd : Region.Disjoint (bufR b) ⟨D, 16 * n⟩)
    (hb : ∀ i < t, ∀ x < 16, s₁.mem (bufAddr b i + BitVec.ofNat 64 x) = (F (k + i)).getD x 0) {j : Nat} (hj : j < t)
    {s : State} (h : CO s₁ m₀ b D n k t F j s) :
    WP isa (.block copyOut) s fun s' => CO s₁ m₀ b D n k t F (j + 1) s' ∧
      X86_64.eval .ne s' = some (decide (t - (j + 1) ≠ 0)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rax, h.wr, ← bufAddr_eq]
    obtain ⟨R, hR, hc⟩ := hbuf j (by omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have hout : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rcx, h.wr]
    exact ⟨_, hD, Offset.contains_base _ (by omega) (by omega)⟩
  have ecnt : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (t - (j + 1)) := by
    rw [h.r10, show t - j = t - (j + 1) + 1 by omega, subOne]
  have hv : ∀ x < 16, (s.mem.readW (bufAddr b j) 128).extractLsb' (8 * x) 8 = (F (k + j)).getD x 0 := fun x hx => by
    rw [readW128_byte _ _ hx, ← hb j hj x hx]
    refine h.frame.bytes (R := ⟨bufAddr b j, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hx
    rw [List.mem_singleton.mp hr]
    exact hd.sub_left fun y hy => by
      simp only [Region.Contains, bufR, bufAddr, bufSlot] at hy ⊢
      bv_omega
  obtain ⟨hp, hf⟩ := Processed.store hn (by omega) h.done hv
  apply WP.of_runBlock
  simp only [copyOut, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load128,
    State.store128, ea_at, hin, hout, ite_true, Option.map_some, Option.bind_some, gpr_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm,
    gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, fun x a c d => ?_, h.rd, h.wr, ?_, ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rcx]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rax]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false]; exact h.gpr x a c d
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, add00, ← bufAddr_eq, writeW128]
    exact h.frame.trans hf
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, add00, ← bufAddr_eq, writeW128]
    exact hp
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem copyOut_loop {s₁ : State} {m₀ : Mem} {b D : Addr} {n k t : Nat} {F : Nat → Spec.Aes.State} (ht : t ≤ 8)
    (h0 : 0 < t) (hkt : k + t ≤ n) (hn : 16 * n ≤ 2 ^ 64) (hD : ⟨D, 16 * n⟩ ∈ s₁.wr)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16) (hd : Region.Disjoint (bufR b) ⟨D, 16 * n⟩)
    (hb : ∀ i < t, ∀ x < 16, s₁.mem (bufAddr b i + BitVec.ofNat 64 x) = (F (k + i)).getD x 0) {s : State}
    (h : CO s₁ m₀ b D n k t F 0 s) : WP isa (.loop (.block copyOut) .ne) s (CO s₁ m₀ b D n k t F t) := by
  let I : Nat → State → Prop := fun c s => ∃ j, c = t - j ∧ j < t ∧ CO s₁ m₀ b D n k t F j s
  refine WP.loop (M := isa) I ?_ t s ⟨0, rfl, h0, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (copyOut_ok ht hkt hn hD hbuf hd hb hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : t - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = t by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

theorem bufR_sub (b : Addr) : Region.Sub (bufR b) ⟨b, 1480⟩ := sub_scratch b (by decide)

theorem low416_sub (b : Addr) : Region.Sub ⟨b, 416⟩ ⟨b, 1480⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢; omega

end VG.Proof.Aes.X86_64.Sse

end
