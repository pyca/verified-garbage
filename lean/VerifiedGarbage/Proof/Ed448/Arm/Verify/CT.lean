import VerifiedGarbage.Proof.Ed448.Arm.Verify.Body
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# Ed448 verification on ARMv7: constant time

As Ed25519's complete operations on this target: two runs from the same
pointers, lengths and `sp` set up the same arguments for every call
(`setup_ct`, `next_setup_ct`), each callee is constant time under its own
contract (`call_ct`), and the blocks between the calls address memory only
through `sp`, `r12` and `scratch` (`hdr_ct`, `zero_ct`). The positions the
absorptions return, which the next ones start from, depend only on the
lengths (`absorb_ct`).
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.rel_wp Whole.setup_ct Whole.callEx Whole.CallReady
  Whole.block_cons_ct Whole.block_nil_ct Whole.step_sp_ct Whole.Within Whole.call_ok)
open VG.Proof.X25519.Arm (wp_mov op2_reg)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok scalarReduce_ct)

/-! ## Relational frame -/

abbrev Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ m₁ a ∧ P a) ∧ (Ctx L g₂ m₂ b ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = argValue L (stk[j]'hj)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid v) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩

/-- A set-up after the position the previous call returned is moved into `r2`. -/
theorem next_setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid v) (h2 : Reg.r2 ∉ args.map Prod.fst) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P)
      (.block (.mov .r2 (.reg .r0) :: setup args stk))
      (Two L g₁ g₂ m₁ m₂ (Slots L ((.r2, .const P) :: args) stk)) := by
  have side : ∀ (g : Reg → BitVec 32) (m : Mem), Arguments L m → ∀ t, Ctx L g m t →
      t.gpr .r0 = BitVec.ofNat 32 P → WP isa (.block (.mov .r2 (.reg .r0) :: setup args stk)) t
        fun u => Ctx L g m u ∧ Slots L ((.r2, .const P) :: args) stk u := by
    intro g m ha t hc h0
    refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
    have hc1 : Ctx L g m s1 := hc.regs v1.rd v1.wr v1.sp
      (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
    refine WP.mono (setup_ok hc1 hL ha hn hv hr hs hvs) fun u ⟨hu, _, hg, ht, hk⟩ => ⟨hu, ?_, ht⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hk .r2 h2 (by decide) (by decide), v1.gpr, h0]; rfl
    · exact hg p hp
  refine Whole.rel_wp ((Whole.step_sp_ct (fun _ _ _ => rfl) (Whole.setup_ct args stk)).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, h0⟩; exact side _ _ ha t hc h0
  · intro t ⟨hc, h0⟩; exact side _ _ hb t hc h0

theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa}
    {name : String} {Q : State → Prop}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (ready : ∀ t, t.sp = L.E → Slots L args stk t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    (hq : ∀ (g : Reg → BitVec 32) (m : Mem) (t : State), Ctx L g m t → Slots L args stk t →
      WP isa (.call name c) t fun u => Ctx L g m u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) (.call name c) (Two L g₁ g₂ m₁ m₂ Q) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine (Whole.callEx correct ct fun a b h => ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_ ?_, ca, wa, cb, wb⟩
    · intro p hp
      rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.1 p hp, h.2.2.1 p hp]
    · intro j hj
      exact (h.1.2.2 j hj).trans (h.2.2.2 j hj).symm
  · intro t ⟨hc, hs⟩; exact hq _ _ t hc hs
  · intro t ⟨hc, hs⟩; exact hq _ _ t hc hs

/-! ## The sponge functions -/

def abs_ready (hL : L.Ok) {t : State} (he : t.sp = L.E) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : DataOk L ⟨State.addr P, N.toNat⟩) (hs : ∀ r ∈ kWr L, Region.Disjoint ⟨State.addr P, N.toNat⟩ r)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : t.gpr .r3 = P) (a0 : stackArg t 0 = N) (a1 : stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR) :
    Whole.CallReady Proof.Sha3.absorbArm L.E L.inputs L.outputs t :=
  ⟨absRd L ⟨State.addr P, N.toNat⟩, kWr L, abs_pre hL hp hs hfit he h0 h1 h2 h3 a0 a1, abs_covers hcov,
    kWr_writes L⟩

/-- An absorption, from arguments that depend only on the layout. -/
theorem absorb_ct (hL : L.Ok) {args : List (Reg × Value)} {vpos vsrc vlen : Value} {pos : Nat}
    (hp : pos < 136) (m0 : (.r0, scr 0) ∈ args) (m1 : (.r1, .const 136) ∈ args) (m2 : (.r2, vpos) ∈ args)
    (m3 : (.r3, vsrc) ∈ args) (hl : ∀ p ∈ args, p.1 ∉ linkRegs) (epos : argValue L vpos = BitVec.ofNat 32 pos)
    (hcov : DataOk L ⟨State.addr (argValue L vsrc), (argValue L vlen).toNat⟩)
    (hs : ∀ r ∈ kWr L, Region.Disjoint ⟨State.addr (argValue L vsrc), (argValue L vlen).toNat⟩ r)
    (hfit : (argValue L vsrc).toNat + (argValue L vlen).toNat ≤ 2 ^ 32) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L args [vlen, scr KSCR]))
      (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb)
      (Two L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((pos + (argValue L vlen).toNat) % 136)) := by
  have get : ∀ t, Slots L args [vlen, scr KSCR] t → t.gpr .r0 = L.scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 pos ∧ t.gpr .r3 = argValue L vsrc ∧ stackArg t 0 = argValue L vlen ∧
      stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    refine ⟨?_, hs.1 _ m1, (hs.1 _ m2).trans epos, hs.1 _ m3, hs.2 0 (by simp), ?_⟩
    · have h := hs.1 _ m0
      simpa only [argValue, scr, Lay.value, BitVec.add_zero] using h
    · exact hs.2 1 (by simp)
  apply call_ct Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h; abs_ready hL he hp hcov hs hfit h0 h1 h2 h3 a0 a1)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg _ m0, hg _ m1, hg _ m2, hg _ m3, ht 0 (by simp), ht 1 (by simp)⟩
  · exact hl
  · intro g m t hc hsl
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hsl
    exact WP.mono (absorb_call hc hL hp hcov hs hfit h0 h1 h2 h3 a0 a1) fun _ ⟨hu, _, hr⟩ => ⟨hu, hr⟩

def padValues (P : Nat) : List (Reg × Value) :=
  [(.r2, .const P), (.r0, scr 0), (.r1, .const 136), (.r3, .const 0x1f)]

theorem pad_ct (hL : L.Ok) {P : Nat} (hp : P < 136) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L (padValues P) [scr KSCR]))
      (.call Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots L (padValues P) [scr KSCR] t → t.gpr .r0 = L.scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 P ∧ stackArg t 0 = L.scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, scr 0) (by simp [padValues])
    have a0 := hs.2 0 (by simp)
    simp only [argValue, scr, Lay.value, BitVec.add_zero, List.getElem_cons_zero] at h0 a0
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [padValues]), hs.1 (.r2, .const P) (by simp [padValues]), a0⟩
  apply call_ct Proof.Sha3.Arm.Stream.Pad.pad_verified.1 Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, a0⟩ := get t h; ⟨[kArgs L 4], kWr L, pad_pre hL hp he h0 h1 h2 a0,
      pad_covers L, kWr_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, scr 0) (by simp [padValues]), hg (.r1, .const 136) (by simp [padValues]),
      hg (.r2, .const P) (by simp [padValues]), hg (.r3, .const 0x1f) (by simp [padValues]), ht 0 (by simp)⟩
  · simp [padValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, a0⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
      (pad_pre hL hp hc.sp h0 h1 h2 a0) (pad_covers L) (kWr_writes L) fun v hv _ _ => ⟨hv, trivial⟩

def sqzValues : List (Reg × Value) := [(.r0, scr 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HASH)]
def sqzStack : List Value := [.const 114, scr KSCR]

theorem sqz_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L sqzValues sqzStack))
      (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots L sqzValues sqzStack t → t.gpr .r0 = L.scr ∧ t.gpr .r1 = 136 ∧ t.gpr .r2 = 0 ∧
      t.gpr .r3 = L.E + BitVec.ofNat 32 HASH ∧ stackArg t 0 = 114 ∧ stackArg t 1 = L.scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, scr 0) (by simp [sqzValues])
    have a0 := hs.2 0 (by simp [sqzStack])
    have a1 := hs.2 1 (by simp [sqzStack])
    simp only [sqzStack, argValue, scr, Lay.value, BitVec.add_zero, List.getElem_cons_zero,
      List.getElem_cons_succ] at h0 a0 a1
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [sqzValues]), hs.1 (.r2, .const 0) (by simp [sqzValues]),
      hs.1 (.r3, .frame HASH) (by simp [sqzValues]), a0, a1⟩
  apply call_ct Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h; ⟨[kArgs L 8], sqzWr L,
      sqz_pre hL he h0 h1 h2 h3 a0 a1, sqz_covers L, sqz_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, scr 0) (by simp [sqzValues]), hg (.r1, .const 136) (by simp [sqzValues]),
      hg (.r2, .const 0) (by simp [sqzValues]), hg (.r3, .frame HASH) (by simp [sqzValues]),
      ht 0 (by simp [sqzStack]), ht 1 (by simp [sqzStack])⟩
  · simp [sqzValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
      (sqz_pre hL hc.sp h0 h1 h2 h3 a0 a1) (sqz_covers L) (sqz_writes L) fun v hv _ _ => ⟨hv, trivial⟩

/-! ## The challenge and the equation -/

def reduceValues : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, scr 0)]

theorem reduce_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L reduceValues []))
      (.call "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots L reduceValues [] t → ReduceArgs L t := by
    intro t hs
    have h2 := hs.1 (.r2, scr 0) (by simp [reduceValues])
    simp only [argValue, scr, Lay.value, BitVec.add_zero] at h2
    exact ⟨hs.1 (.r0, .frame K) (by simp [reduceValues]), hs.1 (.r1, .frame HASH) (by simp [reduceValues]), h2⟩
  apply call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[hReg L], [kReg L, L.SCR], reduce_pre hL (get t h), reduce_covers L, reduce_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .frame K) (by simp [reduceValues]), hg (.r1, .frame HASH) (by simp [reduceValues]),
      hg (.r2, scr 0) (by simp [reduceValues])⟩
  · simp [reduceValues, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL (get t hs)) (reduce_covers L)
      (reduce_writes L) fun v hv _ _ => ⟨hv, trivial⟩

def equationValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)]

theorem equation_ct (hv : EqOk) (hct : EqCT) (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L equationValues []))
      (.call "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots L equationValues [] t → EqArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .caller 0 0) (by simp [equationValues])
    have h1 := hs.1 (.r1, .caller 5 0) (by simp [equationValues])
    have h3 := hs.1 (.r3, scr 0) (by simp [equationValues])
    simp only [argValue, scr, Lay.value, BitVec.add_zero] at h0 h1 h3
    exact ⟨h0, h1, hs.1 (.r2, .frame K) (by simp [equationValues]), h3⟩
  apply call_ct hv hct
    (fun t _ h => ⟨[L.PK, L.SIG, kReg L], [L.SCR], equation_pre hL (get t h), equation_covers L,
      equation_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hg (.r0, .caller 0 0) (by simp [equationValues]), hg (.r1, .caller 5 0) (by simp [equationValues]),
      hg (.r2, .frame K) (by simp [equationValues]), hg (.r3, scr 0) (by simp [equationValues]), hsp⟩
  · simp [equationValues, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc hv equation_noFrames (equation_pre hL (get t hs)) (equation_covers L)
      (equation_writes L) fun v hv' _ _ => ⟨hv', trivial⟩

/-! ## The blocks -/

/-- Stores through `r0`, which they leave alone. -/
theorem stores_ct (ks : List Nat) :
    RelCT isa (fun a b => a.gpr .r0 = b.gpr .r0) (.block (ks.map fun k => Instr.str .r1 .r0 (4 * k)))
      (fun a b => a.gpr .r0 = b.gpr .r0) := by
  induction ks with
  | nil => exact Whole.block_nil_ct
  | cons k ks ih =>
    refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ⟨by simp only [addrs, hp], ?_⟩) ih
    rw [exec_gpr (by simp [dstOf]) ea, exec_gpr (by simp [dstOf]) eb, hp]

theorem zero_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L zeroValues []))
    (.block Impl.Ed448.Arm.PublicKey.zeroStores) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((stores_ct (List.range 50)).mono
    (fun _ _ h => (zero_slots h.1.2.1).1.trans (zero_slots h.2.2.1).1.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_step hc hL (zero_slots hs.1).1 (zero_slots hs.1).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_step hc hL (zero_slots hs.1).1 (zero_slots hs.1).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- Instructions that address memory only through `r12`, and leave it alone. -/
theorem r12_ct (is : List Instr) (hd : ∀ i ∈ is, dstOf i ≠ some .r12)
    (ha : ∀ i ∈ is, ∀ a b : State, a.gpr .r12 = b.gpr .r12 → addrs i a = addrs i b) :
    RelCT isa (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) (.block is)
      (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) := by
  induction is with
  | nil => exact Whole.block_nil_ct
  | cons i is ih =>
    refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ⟨ha i List.mem_cons_self a b hp.2,
      (exec_sp ea).trans (hp.1.trans (exec_sp eb).symm), ?_⟩)
      (ih (fun j hj => hd j (List.mem_cons_of_mem _ hj)) (fun j hj => ha j (List.mem_cons_of_mem _ hj)))
    rw [exec_gpr (hd i List.mem_cons_self) ea, exec_gpr (hd i List.mem_cons_self) eb, hp.2]

def hdrTail : List Instr :=
  [.str .r0 .r12 8, .movw .r0 0x6953, .movt .r0 0x4567, .str .r0 .r12 0,
    .movw .r0 0x3464, .movt .r0 0x3834, .str .r0 .r12 4]

theorem hdr_sp_ct : RelCT isa (fun a b => a.sp = b.sp) (.block hdr) (fun a b => a.sp = b.sp) := by
  have tail : RelCT isa (fun a b => a.sp = b.sp) (.block (.addSp .r12 HDR :: hdrTail))
      (fun a b => a.sp = b.sp) := by
    refine Whole.block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
      (fun a b a' b' hp ea eb => ?_) ((r12_ct hdrTail (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
    · simp only [exec, HDR, show 24 < 256 from by decide, ite_true, Option.some.injEq] at ea eb
      subst a' b'
      exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 24) hp⟩
    · intro i hi a b h
      simp only [hdrTail, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]
  exact Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) (Whole.step_sp_ct (fun _ _ _ => rfl) tail)

theorem hdr_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block hdr)
      (Two L g₁ g₂ m₁ m₂ fun s => Spec.Ed448.bytesAt s.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L) := by
  refine Whole.rel_wp (hdr_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact hdr_ok hc hL ha
  · intro t ⟨hc, _⟩; exact hdr_ok hc hL hb

/-! ## The body -/

/-- An absorption of input data at the position the previous one returned. -/
theorem next_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : valid src) (vl : valid len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argValue L src), (argValue L len).toNat⟩ R)
    (hfit : (argValue L src).toNat + (argValue L len).toNat ≤ 2 ^ 32) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs src len))
      (Two L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argValue L len).toNat) % 136)) := by
  refine (next_setup_ct hL ha hb P [(.r0, scr 0), (.r1, .const 136), (.r3, src)] [len, scr KSCR] (by simp) ?_
    (by simp [preserved]) (by simp) ?_ (by simp)).seq
    (absorb_ct hL hP (vpos := .const P) (by simp) (by simp) (by simp) (by simp) (by simp [linkRegs]) rfl (.inr ⟨R, hR, hw⟩)
      (data_input hL hR hw).1 hfit)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨.inr rfl, by decide⟩
    · show 136 < 65536; decide
    · exact vs
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact vl
    · exact ⟨.inr rfl, by decide⟩

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb zeroValues []
    (by decide) (by simp [zeroValues, valid, scr, Slot]) (by simp [zeroValues, preserved]) (by decide) (by simp)
  have h := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb
    [(.r0, scr 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HDR)] [.const 10, scr KSCR]
    (by decide) (by simp [valid, scr, Slot, HDR]) (by simp [preserved]) (by decide) (by simp [valid, scr, Slot, KSCR])
  have hpd : State.addr (L.E + BitVec.ofNat 32 HDR) = State.addr L.E + BitVec.ofNat 64 HDR := frame_addr hL (by decide)
  have a1 := absorb_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL (pos := 0)
    (args := [(.r0, scr 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HDR)])
    (vpos := .const 0) (vsrc := .frame HDR) (vlen := .const 10) (by decide) (by simp) (by simp) (by simp) (by simp)
    (by simp [linkRegs]) rfl
    (by simp only [argValue]; rw [hpd]; exact .inl ⟨HDR, rfl, by change 24 + 10 ≤ 248; decide⟩)
    (by simp only [argValue]; rw [hpd]; exact (data_frame hL (by decide) (by decide)).1)
    (by simp only [argValue]; exact frame_fit hL (by decide))
  let P1 : Nat := (0 + (argValue L (.const 10)).toNat) % 136
  have x2 := next_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 1 0)
    (len := .caller 2 0) ⟨.inl (by decide), by decide⟩ ⟨.inl (by decide), by decide⟩ (R := L.CTX)
    (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argValue L (.caller 2 0)).toNat) % 136
  have x3 := next_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := .const 57) ⟨.inl (by decide), by decide⟩ (show 57 < 65536 by decide) (R := L.SIG)
    (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; have := hL.ns; simp; omega)
  let P3 : Nat := (P2 + (argValue L (.const 57)).toNat) % 136
  have x4 := next_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 0 0)
    (len := .const 57) ⟨.inl (by decide), by decide⟩ (show 57 < 65536 by decide) (R := L.PK)
    (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega)
  let P4 : Nat := (P3 + (argValue L (.const 57)).toNat) % 136
  have x5 := next_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨.inl (by decide), by decide⟩ ⟨.inl (by decide), by decide⟩ (R := L.MSG)
    (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argValue L (.caller 4 0)).toNat) % 136
  have pd := (next_setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P5 [(.r0, scr 0), (.r1, .const 136), (.r3, .const 0x1f)]
    [scr KSCR] (by decide) (by simp [valid, scr, Slot]) (by simp [preserved]) (by decide)
    (by simp [valid, scr, Slot, KSCR]) (by decide)).seq (pad_ct hL (P := P5) (Nat.mod_lt _ (by decide)))
  have sq := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb sqzValues sqzStack (by decide)
    (by simp [sqzValues, valid, scr, Slot, HASH]) (by simp [sqzValues, preserved]) (by decide)
    (by simp [sqzStack, valid, scr, Slot, KSCR])).seq (sqz_ct hL)
  exact (z.seq (zero_ct hL)).seq ((h.seq a1).seq (x2.seq (x3.seq (x4.seq (x5.seq (pd.seq sq))))))

theorem body_ct (hv : EqOk) (hct : EqCT) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb reduceValues [] (by decide)
    (by simp [reduceValues, valid, scr, Slot, K, HASH]) (by simp [reduceValues, preserved]) (by decide)
    (by simp)).seq (reduce_ct hL)
  have e := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb equationValues [] (by decide)
    (by simp [equationValues, valid, scr, Slot, K]) (by simp [equationValues, preserved]) (by decide)
    (by simp)).seq (equation_ct hv hct hL)
  exact ((hdr_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)).seq
    ((hash_ct hL ha hb).seq (r.seq e))

end VG.Proof.Ed448.Arm.Verify
