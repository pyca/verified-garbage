import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 public-key derivation on ARMv7: constant time, and `Verified`

As Ed25519's on this target (`Proof/Ed25519/Arm/PublicKey/Verified.lean`):
two runs from the same pointers and `sp` set up the same arguments for every
call (`setup_ct`), each callee is constant time under its own contract
(`call_ct`), and the blocks between the calls address memory only through
`sp`, `scratch` and the frame (`zero_ct`, `prune_ct`, `wipe_ct`).
`publicKey_verified` takes the reference ladder's agreement with the
specification (`BaseLadderOk`) as a hypothesis.
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.rel_wp Whole.setup_ct Whole.callEx Whole.CallReady
  Whole.block_cons_ct Whole.block_nil_ct Whole.zeroWords_ct Whole.wrap_ct Whole.base
  Whole.bodyRd Whole.bodyWr Whole.valid)
open VG.Proof.Ed448 (BaseLadderOk)

/-! ## Relational frame -/

abbrev Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ m₁ a ∧ P a) ∧ (Ctx L g₂ m₂ b ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = argValue L (stk[j]'hj)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩

theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ t, t.sp = L.E → Slots L args stk t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) (.call name c)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
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
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩

/-! ## The calls -/

section
variable {t : State}

def abs_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L absValues absStack t) :
    Whole.CallReady Proof.Sha3.absorbArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [absValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [absValues])
  have h2 := hs.1 (.r2, .const 0) (by simp [absValues])
  have h3 := hs.1 (.r3, .caller 1 0) (by simp [absValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [absStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  exact ⟨absRd L, kWr L, abs_pre hL he h0 h1 h2 h3 a0 a1, abs_covers L, kWr_writes L⟩

def pad_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L padValues padStack t) :
    Whole.CallReady Proof.Sha3.padArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [padValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [padValues])
  have h2 := hs.1 (.r2, .const 57) (by simp [padValues])
  have a0 := hs.2 0 (by decide)
  simp only [padStack, argValue, Lay.value, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h2 a0
  exact ⟨[kArgs L 4], kWr L, pad_pre hL he h0 h1 h2 a0, pad_covers L, kWr_writes L⟩

def sqz_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L sqzValues sqzStack t) :
    Whole.CallReady Proof.Sha3.squeezeArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [sqzValues])
  have h1 := hs.1 (.r1, .const 136) (by simp [sqzValues])
  have h2 := hs.1 (.r2, .const 0) (by simp [sqzValues])
  have h3 := hs.1 (.r3, .frame HASH) (by simp [sqzValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [sqzStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  exact ⟨[kArgs L 8], sqzWr L, sqz_pre hL he h0 h1 h2 h3 a0 a1, sqz_covers L, sqz_writes L⟩

def base_ready (hL : L.Ok) (hs : Slots L baseValues [] t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 0 0) (by simp [baseValues])
  have h1 := hs.1 (.r1, .frame HASH) (by simp [baseValues])
  have h2 := hs.1 (.r2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨hq L, 57⟩], L.outputs, base_pre hL ⟨h0, h1, h2⟩, base_covers L, base_writes L⟩

end

theorem abs_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L absValues absStack))
    (.call Spec.Sha3.absorbApi.name Impl.Sha3.Arm.Stream.absorb) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
    Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1 absorb_noFrames (fun _ he h => abs_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [absValues]), hg (.r1, .const 136) (by simp [absValues]),
      hg (.r2, .const 0) (by simp [absValues]), hg (.r3, .caller 1 0) (by simp [absValues]),
      ht 0 (by decide), ht 1 (by decide)⟩
  · simp [absValues, linkRegs]

theorem pad_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L padValues padStack))
    (.call Spec.Sha3.padApi.name Impl.Sha3.Arm.Stream.pad) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha3.Arm.Stream.Pad.pad_verified.1
    Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1 pad_noFrames (fun _ he h => pad_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [padValues]), hg (.r1, .const 136) (by simp [padValues]),
      hg (.r2, .const 57) (by simp [padValues]), hg (.r3, .const 0x1f) (by simp [padValues]),
      ht 0 (by decide)⟩
  · simp [padValues, linkRegs]

theorem sqz_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L sqzValues sqzStack))
    (.call Spec.Sha3.squeezeApi.name Impl.Sha3.Arm.Stream.squeeze) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1 squeeze_noFrames (fun _ he h => sqz_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [sqzValues]), hg (.r1, .const 136) (by simp [sqzValues]),
      hg (.r2, .const 0) (by simp [sqzValues]), hg (.r3, .frame HASH) (by simp [sqzValues]),
      ht 0 (by decide), ht 1 (by decide)⟩
  · simp [sqzValues, linkRegs]

theorem base_ct (hl : BaseLadderOk) (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L baseValues []))
    (.call "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (scalarBase_ok hl) scalarBase_ct base_noFrames (fun _ _ h => base_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hg (.r0, .caller 0 0) (by simp [baseValues]), hg (.r1, .frame HASH) (by simp [baseValues]),
      hg (.r2, .caller 2 0) (by simp [baseValues]), hsp⟩
  · simp [baseValues, linkRegs]

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
    (.block zeroStores) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r0 : ∀ {s : State}, Slots L zeroValues [] s → s.gpr .r0 = L.scr := fun hs => by
    have h := hs.1 (.r0, .caller 2 0) (by simp [zeroValues])
    simpa only [argValue, Lay.value, BitVec.add_zero] using h
  have r1 : ∀ {s : State}, Slots L zeroValues [] s → s.gpr .r1 = 0 := fun hs => by
    have h := hs.1 (.r1, .const 0) (by simp [zeroValues])
    exact h
  refine Whole.rel_wp ((stores_ct (List.range 50)).mono
    (fun _ _ h => (r0 h.1.2).trans (r0 h.2.2).symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_step hc hL (r0 hs) (r1 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_step hc hL (r0 hs) (r1 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

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

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) prune (fun a b => a.sp = b.sp) := by
  unfold prune
  refine RelCT.seq (M := isa) (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) ?_
    ((r12_ct pruneOps (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
  · refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ?_) Whole.block_nil_ct
    simp only [exec, HASH, show 24 < 256 from by decide, ite_true, Option.some.injEq] at ea eb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 24) hp⟩
  · intro i hi a b h
    simp only [pruneOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]

theorem prune_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) prune
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-! ## The whole function -/

theorem body_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb zeroValues []
    (by decide) (by simp [zeroValues, Whole.valid]) (by simp [zeroValues])
    (by simp [zeroValues, preserved]) (by decide) (by simp) (by simp)
  have a := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb absValues absStack
    (by decide) (by simp [absValues, Whole.valid]) (by simp [absValues])
    (by simp [absValues, preserved]) (by decide) (by simp [absStack, Whole.valid, KSCR])
    (by simp [absStack])
  have p := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb padValues padStack
    (by decide) (by simp [padValues, Whole.valid]) (by simp [padValues])
    (by simp [padValues, preserved]) (by decide) (by simp [padStack, Whole.valid, KSCR])
    (by simp [padStack])
  have q := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb sqzValues sqzStack
    (by decide) (by simp [sqzValues, Whole.valid, HASH]) (by simp [sqzValues])
    (by simp [sqzValues, preserved]) (by decide) (by simp [sqzStack, Whole.valid, KSCR])
    (by simp [sqzStack])
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb baseValues []
    (by decide) (by simp [baseValues, Whole.valid, HASH]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by decide) (by simp) (by simp)
  exact ((z.seq (zero_ct hL)).seq ((a.seq (abs_ct hL)).seq ((p.seq (pad_ct hL)).seq (q.seq (sqz_ct hL))))).seq
    ((prune_ct hL).seq ((b.seq (base_ct hl hL)).seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (hl : BaseLadderOk) : ConstantTime isa pkLocal.pre pkLocal.pub code := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    exact WP.mono (body_ok hl (entry_ctx hs hp) (lay_ok hs) (entry_args (entry_below hs) hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args (entry_below ht) hqb
    exact ⟨(body_ct hl (lay_ok hs) (entry_args (entry_below hs) hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed448.publicKeyContract Arm.abi 280) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, pkLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState] using satState

/-- `vg_ed448_public_key` on ARMv7, given the reference ladder's agreement
with the specification. -/
theorem publicKey_verified (hl : BaseLadderOk) :
    Verified Arm.target code (Spec.Ed448.publicKeyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok hl h) (publicKey_ct hl) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed448.Arm.PublicKey
