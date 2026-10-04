import VerifiedGarbage.Proof.Ed448.Arm.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Header
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified

/-!
# Ed448 on ARMv7: the calls of the sponge functions in constant time

As Ed25519's complete operations on this target: two runs from the same
pointers, lengths and `sp` set up the same arguments for every call
(`setup_ct`, `next_setup_ct`), each callee is constant time under its own
contract (`call_ct`), and the blocks between the calls address memory only
through `sp`, `r12` and `scratch` (`hdr_ct`, `zero_ct`). The positions the
absorptions return, which the next ones start from, depend only on the
lengths (`absorb_ct`).
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.rel_wp Whole.setup_ct Whole.callEx Whole.CallReady
  Whole.block_cons_ct Whole.block_nil_ct Whole.step_sp_ct Whole.Within Whole.Ctx Whole.call_ok)
open VG.Proof.X25519.Arm (wp_mov op2_reg)

/-! ## Relational frame -/

/-- Both runs in the frame, and `P` of each. -/
abbrev Two (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Whole.Ctx E g₁ m₁ ins outs a ∧ P a) ∧ (Whole.Ctx E g₂ m₂ ins outs b ∧ P b)

/-- A call's arguments, in registers and on the stack. -/
def Slots (E : BitVec 32) (val : Nat → BitVec 32) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = argVal E val p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = argVal E val (stk[j]'hj)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

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

/-- The header's block addresses memory only through `sp` and `r12 = sp + off`. -/
theorem hdr_sp_ct (j off : Nat) (ho : off < 256) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (hdrAt j off)) (fun a b => a.sp = b.sp) := by
  have tail : RelCT isa (fun a b => a.sp = b.sp) (.block (.addSp .r12 off :: hdrTail))
      (fun a b => a.sp = b.sp) := by
    refine Whole.block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
      (fun a b a' b' hp ea eb => ?_) ((r12_ct hdrTail (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
    · simp only [exec, ho, ite_true, Option.some.injEq] at ea eb
      subst a' b'
      exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 off) hp⟩
    · intro i hi a b h
      simp only [hdrTail, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]
  exact Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) (Whole.step_sp_ct (fun _ _ _ => rfl) tail)

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

theorem setup_ct (ha : Args E n val m₁) (hb : Args E n val m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid n v) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (hk.setup_ok hc ha hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (hk.setup_ok hc hb hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩

/-- A set-up after the position the previous call returned is moved into `r2`. -/
theorem next_setup_ct (ha : Args E n val m₁) (hb : Args E n val m₂) (P : Nat)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid n v) (h2 : Reg.r2 ∉ args.map Prod.fst) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P)
      (.block (.mov .r2 (.reg .r0) :: setup args stk))
      (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val ((.r2, .const P) :: args) stk)) := by
  have side : ∀ (g : Reg → BitVec 32) (m : Mem), Args E n val m → ∀ t, Whole.Ctx E g m ins outs t →
      t.gpr .r0 = BitVec.ofNat 32 P → WP isa (.block (.mov .r2 (.reg .r0) :: setup args stk)) t
        fun u => Whole.Ctx E g m ins outs u ∧ Slots E val ((.r2, .const P) :: args) stk u := by
    intro g m ha t hc h0
    refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
    have hc1 : Whole.Ctx E g m ins outs s1 := hc.regs v1.rd v1.wr v1.sp
      (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
    refine WP.mono (hk.setup_ok hc1 ha hn hv hr hs hvs) fun u ⟨hu, _, hg, ht, hk'⟩ => ⟨hu, ?_, ht⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hk' .r2 h2 (by decide) (by decide), v1.gpr, h0]; rfl
    · exact hg p hp
  refine Whole.rel_wp ((Whole.step_sp_ct (fun _ _ _ => rfl) (Whole.setup_ct args stk)).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, h0⟩; exact side _ _ ha t hc h0
  · intro t ⟨hc, h0⟩; exact side _ _ hb t hc h0

omit hk in
theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa}
    {name : String} {Q : State → Prop}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (ready : ∀ t, t.sp = E → Slots E val args stk t → Whole.CallReady k E ins outs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    (hq : ∀ (g : Reg → BitVec 32) (m : Mem) (t : State), Whole.Ctx E g m ins outs t → Slots E val args stk t →
      WP isa (.call name c) t fun u => Whole.Ctx E g m ins outs u ∧ Q u) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val args stk)) (.call name c)
      (Two E ins outs g₁ g₂ m₁ m₂ Q) := by
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

/-- An absorption, from arguments that depend only on the layout. -/
theorem absorb_ct {sc : Nat} (hsc : ScrAt n val sc scr) {args : List (Reg × Value)} {vpos vsrc vlen : Value}
    {pos : Nat} (hp : pos < 136) (m0 : (.r0, .caller sc 0) ∈ args) (m1 : (.r1, .const 136) ∈ args)
    (m2 : (.r2, vpos) ∈ args) (m3 : (.r3, vsrc) ∈ args) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    (epos : argVal E val vpos = BitVec.ofNat 32 pos)
    (hcov : DataOk E ins outs ⟨State.addr (argVal E val vsrc), (argVal E val vlen).toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr (argVal E val vsrc), (argVal E val vlen).toNat⟩ r)
    (hfit : (argVal E val vsrc).toNat + (argVal E val vlen).toNat ≤ 2 ^ 32) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val args [vlen, .caller sc KSCR]))
      (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb)
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((pos + (argVal E val vlen).toNat) % 136)) := by
  have get : ∀ t, Slots E val args [vlen, .caller sc KSCR] t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 pos ∧ t.gpr .r3 = argVal E val vsrc ∧ stackArg t 0 = argVal E val vlen ∧
      stackArg t 1 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    refine ⟨?_, hs.1 _ m1, (hs.1 _ m2).trans epos, hs.1 _ m3, hs.2 0 (by simp), ?_⟩
    · have h := hs.1 _ m0
      simpa only [argVal, hsc.val, BitVec.add_zero] using h
    · have h := hs.2 1 (by simp)
      simpa only [argVal, hsc.val, List.getElem_cons_succ, List.getElem_cons_zero] using h
  apply call_ct Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h;
      ⟨absRd E ⟨State.addr (argVal E val vsrc), (argVal E val vlen).toNat⟩, kWr scr,
        hk.abs_pre hp hs hfit he h0 h1 h2 h3 a0 a1, hk.abs_covers hcov, hk.kWr_writes⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg _ m0, hg _ m1, hg _ m2, hg _ m3, ht 0 (by simp), ht 1 (by simp)⟩
  · exact hl
  · intro g m t hc hsl
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hsl
    exact WP.mono (hk.absorb_call hc hp hcov hs hfit h0 h1 h2 h3 a0 a1) fun _ ⟨hu, _, _, hr⟩ => ⟨hu, hr⟩

def padValues (sc P : Nat) : List (Reg × Value) :=
  [(.r2, .const P), (.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)]

theorem pad_ct {sc : Nat} (hsc : ScrAt n val sc scr) {P : Nat} (hp : P < 136) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val (padValues sc P) [.caller sc KSCR]))
      (.call Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots E val (padValues sc P) [.caller sc KSCR] t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 P ∧ stackArg t 0 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, .caller sc 0) (by simp [padValues])
    have a0 := hs.2 0 (by simp)
    simp only [argVal, hsc.val, BitVec.add_zero, List.getElem_cons_zero] at h0 a0
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [padValues]), hs.1 (.r2, .const P) (by simp [padValues]), a0⟩
  apply call_ct Proof.Sha3.Arm.Stream.Pad.pad_verified.1 Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, a0⟩ := get t h; ⟨[kArgs E 4], kWr scr, hk.pad_pre hp he h0 h1 h2 a0,
      hk.pad_covers, hk.kWr_writes⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller sc 0) (by simp [padValues]), hg (.r1, .const 136) (by simp [padValues]),
      hg (.r2, .const P) (by simp [padValues]), hg (.r3, .const 0x1f) (by simp [padValues]), ht 0 (by simp)⟩
  · simp [padValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, a0⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
      (hk.pad_pre hp hc.sp h0 h1 h2 a0) hk.pad_covers hk.kWr_writes fun v hv _ _ => ⟨hv, trivial⟩

def sqzValues (sc d : Nat) : List (Reg × Value) :=
  [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame d)]
def sqzStack (sc : Nat) : List Value := [.const 114, .caller sc KSCR]

theorem sqz_ct {sc : Nat} (hsc : ScrAt n val sc scr) {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val (sqzValues sc d) (sqzStack sc)))
      (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, Slots E val (sqzValues sc d) (sqzStack sc) t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = 0 ∧ t.gpr .r3 = E + BitVec.ofNat 32 d ∧ stackArg t 0 = 114 ∧
      stackArg t 1 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, .caller sc 0) (by simp [sqzValues])
    have a0 := hs.2 0 (by simp [sqzStack])
    have a1 := hs.2 1 (by simp [sqzStack])
    simp only [sqzStack, argVal, hsc.val, BitVec.add_zero, List.getElem_cons_zero,
      List.getElem_cons_succ] at h0 a0 a1
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [sqzValues]), hs.1 (.r2, .const 0) (by simp [sqzValues]),
      hs.1 (.r3, .frame d) (by simp [sqzValues]), a0, a1⟩
  apply call_ct Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h; ⟨[kArgs E 8], sqzWr E scr d,
      hk.sqz_pre h8 hd he h0 h1 h2 h3 a0 a1, hk.sqz_covers hd, hk.sqz_writes hd⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller sc 0) (by simp [sqzValues]), hg (.r1, .const 136) (by simp [sqzValues]),
      hg (.r2, .const 0) (by simp [sqzValues]), hg (.r3, .frame d) (by simp [sqzValues]),
      ht 0 (by simp [sqzStack]), ht 1 (by simp [sqzStack])⟩
  · simp [sqzValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
      (hk.sqz_pre h8 hd hc.sp h0 h1 h2 h3 a0 a1) (hk.sqz_covers hd) (hk.sqz_writes hd) fun v hv _ _ => ⟨hv, trivial⟩

/-! ## The blocks -/

theorem zero_ct {sc : Nat} (hsc : ScrAt n val sc scr) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (Slots E val [(.r0, .caller sc 0), (.r1, .const 0)] []))
      (.block Impl.Ed448.Arm.PublicKey.zeroStores) (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have r0 : ∀ {s : State}, Slots E val [(.r0, .caller sc 0), (.r1, .const 0)] [] s → s.gpr .r0 = scr ∧ s.gpr .r1 = 0 :=
    fun hs => by
      have h0 := hs.1 (.r0, .caller sc 0) (by simp)
      have h1 := hs.1 (.r1, .const 0) (by simp)
      simp only [argVal, hsc.val, BitVec.add_zero] at h0 h1
      exact ⟨h0, h1⟩
  refine Whole.rel_wp ((PublicKey.stores_ct (List.range 50)).mono
    (fun _ _ h => (r0 h.1.2).1.trans (r0 h.2.2).1.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, hs⟩
    exact WP.mono (hk.zeroStores_step hc (r0 hs).1 (r0 hs).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (hk.zeroStores_step hc (r0 hs).1 (r0 hs).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- The state zeroed. -/
theorem zeroState_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (zeroState sc)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.setup_ct ha hb [(.r0, .caller sc 0), (.r1, .const 0)] [] (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp) (by simp)).seq (hk.zero_ct hsc)

theorem hdr_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {j off : Nat} (hj : Slot n j)
    (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 248) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt j off))
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => Spec.Ed448.bytesAt s.mem (State.addr E + BitVec.ofNat 64 off) 10 =
        hdrBytes (val j)) := by
  have hf := hk.fits
  have hj' := hj.1
  refine Whole.rel_wp ((hdr_sp_ct j off (by omega)).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (hk.hdr_ok hc ha hj hcl ho) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩
  · intro t ⟨hc, _⟩; exact WP.mono (hk.hdr_ok hc hb hj hcl ho) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

/-- An absorption at the position the previous one returned. -/
theorem next_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr)
    (P : Nat) (hP : P < 136) {src len : Value} (vs : valid n src) (vl : valid n len)
    (hcov : DataOk E ins outs ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩ r)
    (hfit : (argVal E val src).toNat + (argVal E val len).toNat ≤ 2 ^ 32) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs sc src len))
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal E val len).toNat) % 136)) :=
  (hk.next_setup_ct ha hb P [(.r0, .caller sc 0), (.r1, .const 136), (.r3, src)] [len, .caller sc KSCR] (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), valid_const (by decide), vs, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩) (by simp)).seq
    (hk.absorb_ct hsc hP (vpos := .const P) (by simp) (by simp) (by simp) (by simp) (by simp [linkRegs]) rfl
      hcov hs hfit)

/-- The first absorption, from position 0. -/
theorem first_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr)
    {src len : Value} (vs : valid n src) (vl : valid n len)
    (hcov : DataOk E ins outs ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩)
    (hs : ∀ r ∈ kWr scr, Region.Disjoint ⟨State.addr (argVal E val src), (argVal E val len).toNat⟩ r)
    (hfit : (argVal E val src).toNat + (argVal E val len).toNat ≤ 2 ^ 32) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs sc src len))
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((0 + (argVal E val len).toNat) % 136)) :=
  (hk.setup_ct ha hb [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, src)] [len, .caller sc KSCR]
    (by simp)
    (by simp only [List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), vs, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩)).seq
    (hk.absorb_ct hsc (pos := 0) (vpos := .const 0) (by decide) (by simp) (by simp) (by simp) (by simp)
      (by simp [linkRegs]) rfl hcov hs hfit)

/-- The padding, at the position the last absorption returned. -/
theorem padStep_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr)
    (P : Nat) (hP : P < 136) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (pad sc)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.next_setup_ct ha hb P [(.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)] [.caller sc KSCR]
    (by simp)
    (by simp only [List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), fun _ h => nomatch h⟩) (by simp)).seq
    (hk.pad_ct hsc hP)

/-- 114 bytes squeezed into the frame at `d`. -/
theorem sqzStep_ct (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr)
    {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (squeeze sc d)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.setup_ct ha hb (sqzValues sc d) (sqzStack sc) (by simp [sqzValues])
    (by simp only [sqzValues, List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), valid_const (by decide), valid_const (by decide), valid_frame (by omega),
          fun _ h => nomatch h⟩)
    (by simp [sqzValues, preserved]) (by simp [sqzStack])
    (by simp only [sqzStack, List.forall_mem_cons]
        exact ⟨valid_const (by decide), hsc.valid (by decide), fun _ h => nomatch h⟩)).seq
    (hk.sqz_ct hsc h8 hd)

end Kit

end VG.Proof.Ed448.Arm.Shake
