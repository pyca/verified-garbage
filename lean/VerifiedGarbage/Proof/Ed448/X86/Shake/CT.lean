import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.X86.Shake.Header
import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Ed448 on x86 (32-bit): the calls of the sponge functions in constant time

As Ed25519's complete operations on this target: the blocks between the
calls address memory only through `esp` (`block_ct`, given the taint check
of each block, which its operation discharges with `taint_decide`), two runs
from the same pointers, lengths and `esp` set up the same arguments for
every call (`AbsSlots`, …), and each callee is constant time under its own
contract (`call_ct`). The positions the absorptions return, which the next
ones start from, depend only on the lengths.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (Value setup at_)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.X86 (Whole.CallReady Whole.Ctx Whole.FR Whole.valid Whole.slots Whole.rel_wp
  Whole.callEx Whole.block_rel)

/-- Both runs in the frame, and `P` of each. -/
abbrev Two (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Whole.Ctx E g₁ m₁ ins outs a ∧ P a) ∧ (Whole.Ctx E g₂ m₂ ins outs b ∧ P b)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem two_esp {P : State → Prop} {a b : State} (h : Two E ins outs g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.1.esp.trans h.2.1.esp.symm

/-- A block that addresses memory only through `esp`, with what it does in each run. -/
theorem block_ct {is : List Instr} {P Q : State → Prop} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block is) hint).isSome = true)
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ P) (.block is) (Two E ins outs g₁ g₂ m₁ m₂ Q) :=
  Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ P a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ P b)
    (Whole.block_rel (fun _ _ h => two_esp h) ht) (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)

/-- A block that addresses memory only through the registers `rs`, equal in
both runs. -/
theorem regs_block_ct {is : List Instr} {P Q : State → Prop} {rs : List Reg}
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr rs) (.block is) hint).isSome = true)
    (he : ∀ a b, Two E ins outs g₁ g₂ m₁ m₂ P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ P) (.block is) (Two E ins outs g₁ g₂ m₁ m₂ Q) :=
  Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ P a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ P b)
    (RelCT.taint (A := taint) (τr rs) (fun a b h => agree_regs (he a b h)) ht)
    (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)

/-- A call whose arguments (`R`) are the same in both runs, with what it does in each. -/
theorem call_ct {k : Contract isa} {c : Prog isa} {name : String} {R Q : State → Prop}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (ready : ∀ (g : Reg → BitVec 32) (m : Mem) (t : State), Whole.Ctx E g m ins outs t → R t →
      Whole.CallReady k E ins outs t)
    (kp : ∀ a b : State, a.gpr .esp = E → b.gpr .esp = E → R a → R b → ∀ ar aw br bw,
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → R t →
      WP isa (.call name c) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → R t →
      WP isa (.call name c) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ R) (.call name c) (Two E ins outs g₁ g₂ m₁ m₂ Q) := by
  refine Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ R a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ R b) ?_ (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)
  refine Whole.callEx correct ct fun a b h => ?_
  let ra := ready _ _ a h.1.1 h.1.2
  let rb := ready _ _ b h.2.1 h.2.2
  obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
  obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
  exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
    kp a b h.1.1.esp h.2.1.esp h.1.2 h.2.2 _ _ _ _, ca, wa, cb, wb, two_esp h⟩

theorem entry_esp {a b : State} (ea : a.gpr .esp = E) (eb : b.gpr .esp = E) (ar aw br bw : List Region) :
    (a.callEntry.withRegions ar aw).gpr .esp = (b.callEntry.withRegions br bw).gpr .esp := by
  simp only [State.withRegions_gpr, State.callEntry_esp, ea, eb]

theorem AbsSlots.eq {pos : Nat} {P N : BitVec 32} {a b : State} (ha : AbsSlots E scr pos P N a)
    (hb : AbsSlots E scr pos P N b) : ∀ i < 6, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm, ha.a5.trans hb.a5.symm]

theorem PadSlots.eq {pos : Nat} {a b : State} (ha : PadSlots E scr pos a) (hb : PadSlots E scr pos b) :
    ∀ i < 5, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm]

theorem SqzSlots.eq {d : Nat} {a b : State} (ha : SqzSlots E scr d a) (hb : SqzSlots E scr d b) :
    ∀ i < 6, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm, ha.a5.trans hb.a5.symm]

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

/-- The arguments of two calls, from equal slots. -/
theorem args_eq {a b : State} (ea : a.gpr .esp = E) (eb : b.gpr .esp = E) {k : Nat} (hk6 : k ≤ 6)
    (h : ∀ i < k, Whole.slots E a i = Whole.slots E b i) (ar aw br bw : List Region) :
    ∀ i < k, arg (a.callEntry.withRegions ar aw) i = arg (b.callEntry.withRegions br bw) i := by
  intro i hi
  rw [arg_withRegions, arg_withRegions, VG.Proof.Ed25519.X86.Whole.call_arg ea hk.below hk.frame (by omega),
    VG.Proof.Ed25519.X86.Whole.call_arg eb hk.below hk.frame (by omega)]
  exact h i hi

/-! ## The calls -/

theorem abs_ct {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (AbsSlots E scr pos P N))
      (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb)
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136)) :=
  call_ct Proof.Sha3.X86.Stream.Absorb.absorb_verified.1 Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1
    (fun _ _ _ hc hs => hk.abs_ready hc hp hs hcov hd hfit)
    (fun a b ea eb ha hb ar aw br bw => ⟨entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.absorb_slots hc hp hs hcov hd hfit) fun _ ⟨hv, _, _, he⟩ => ⟨hv, he⟩)
    (fun _ hc hs => WP.mono (hk.absorb_slots hc hp hs hcov hd hfit) fun _ ⟨hv, _, _, he⟩ => ⟨hv, he⟩)

theorem pad_ct {pos : Nat} (hp : pos < 136) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (PadSlots E scr pos))
      (.call Spec.Sha3.padScratchApi.name Impl.Sha3.X86.Stream.pad) (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  call_ct Proof.Sha3.X86.Stream.Pad.pad_verified.1 Proof.Sha3.X86.Stream.Pad.pad_verified.2.1
    (fun _ _ _ hc hs => hk.pad_ready hc hp hs)
    (fun a b ea eb ha hb ar aw br bw => ⟨entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.pad_call hc hp hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)
    (fun _ hc hs => WP.mono (hk.pad_call hc hp hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)

theorem sqz_ct {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ (SqzSlots E scr d))
      (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.X86.Stream.squeeze)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  call_ct Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1 Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1
    (fun _ _ _ hc hs => hk.sqz_ready hc h24 hd hs)
    (fun a b ea eb ha hb ar aw br bw => ⟨entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.sqz_call hc h24 hd hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)
    (fun _ hc hs => WP.mono (hk.sqz_call hc h24 hd hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)

/-! ## The sponge's steps -/

variable (ha : Args E n val m₁) (hb : Args E n val m₂) {sc : Nat} (hsc : ScrAt n val sc scr)
include ha hb hsc

/-- The state zeroed: `scratch`, the same in both runs, loaded into `eax`,
then the stores through it. -/
theorem zero_ct {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (zeroArgs sc)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (zeroState sc) (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  unfold zeroState
  refine RelCT.block_append (RelCT.seq (R := Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = scr ∧ s.gpr .edx = 0)
    (block_ct ht (fun _ hc _ => WP.mono (hk.zeroArgs_ok hc ha hsc) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun _ hc _ => WP.mono (hk.zeroArgs_ok hc hb hsc) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)) ?_)
  refine regs_block_ct (rs := [.esp, .eax]) (by taint_decide) (fun a b h r hr => ?_)
    (fun _ hc h => WP.mono (hk.zeroStores_step hc h.1 h.2) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc h => WP.mono (hk.zeroStores_step hc h.1 h.2) fun _ h => ⟨h.1, trivial⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact two_esp h
  · exact h.1.2.1.trans h.2.2.1.symm

/-- The first absorption, from position 0. -/
theorem first_ct {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (firstArgs sc src len)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs sc src len))
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 (N % 136)) := by
  subst hP hN
  refine RelCT.seq (block_ct ht (fun _ hc _ => WP.mono (hk.first_setup hc ha hsc vs vl) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc _ => WP.mono (hk.first_setup hc hb hsc vs vl) fun _ h => ⟨h.1, h.2.2⟩)) ?_
  have h := hk.abs_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) (by decide : 0 < 136) hcov hd hfit
  rwa [Nat.zero_add] at h

/-- An absorption at the position `pos` the previous one returned. -/
theorem next_ct {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : argVal E val src = P) (hN : (argVal E val len).toNat = N)
    (hcov : DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) {pos : Nat} (hp : pos < 136) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (nextArgs sc src len)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 pos) (absorb (nextArgs sc src len))
      (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 ((pos + N) % 136)) := by
  subst hP hN
  exact RelCT.seq (block_ct ht (fun _ hc h0 => WP.mono (hk.next_setup hc ha hsc vs vl h0) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc h0 => WP.mono (hk.next_setup hc hb hsc vs vl h0) fun _ h => ⟨h.1, h.2.2⟩))
    (hk.abs_ct hp hcov hd hfit)

/-- The padding, at the position `pos` the last absorption returned. -/
theorem padStep_ct {pos : Nat} (hp : pos < 136) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (padArgs sc)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 pos) (pad sc)
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  RelCT.seq (block_ct ht (fun _ hc h0 => WP.mono (hk.pad_setup hc ha hsc h0) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc h0 => WP.mono (hk.pad_setup hc hb hsc h0) fun _ h => ⟨h.1, h.2.2⟩)) (hk.pad_ct hp)

/-- 114 bytes squeezed into the frame at `d`. -/
theorem sqzStep_ct {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (sqzArgs sc d)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (squeeze sc d) (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  RelCT.seq (block_ct ht (fun _ hc _ => WP.mono (hk.sqz_setup hc ha hsc d) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc _ => WP.mono (hk.sqz_setup hc hb hsc d) fun _ h => ⟨h.1, h.2.2⟩)) (hk.sqz_ct h24 hd)

omit hsc in
/-- The header of `dom4` in the frame at `off`. -/
theorem hdr_ct {j off : Nat} (hj : j < n) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 256)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (hdrAt j off)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt j off))
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  block_ct ht (fun _ hc _ => WP.mono (hk.hdr_ok hc ha hj hcl ho) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc _ => WP.mono (hk.hdr_ok hc hb hj hcl ho) fun _ h => ⟨h.1, trivial⟩)

omit ha hb hsc in
/-- The hash at `q` pruned in place. -/
theorem prune_ct {q : Nat} (hq : q + 57 ≤ 256) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (pruneAt q)) hint).isSome = true) :
    RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (pruneAt q))
      (Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  block_ct ht (fun _ hc _ => WP.mono (hk.prune_ok hc hq) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc _ => WP.mono (hk.prune_ok hc hq) fun _ h => ⟨h.1, trivial⟩)

end Kit

end VG.Proof.Ed448.X86.Shake
