module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Draw
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CT
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# A draw leaks only its public bounds and its decision (x86)

Two runs of `draw` with the same public data, consumption and budget, whose
complete draws are both accepted or both rejected (`DrawPub.acc`), take
the same branches and addresses: the candidate's bytes reach neither.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The candidate of the draw at `used`. -/
abbrev drawCand (s₀ : State) (used : Nat) : List Byte :=
  copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)

/-- What two runs of a draw share. -/
structure DrawPub where
  pub : Pub
  used : Nat
  draws : Nat
  /-- Whether a complete draw is accepted. -/
  acc : Bool

/-- A draw's entry. -/
structure DrawPre (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : a.used + rWidth s₀ ≤ (rInput s₀).rand.length → accepts s₀ (drawCand s₀ a.used) = a.acc

theorem width_pos {s₀ : State} (hq : 1 < rq s₀) : 1 ≤ rWidth s₀ :=
  Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1

/-- `esp` is pinned by a predicate about the frame. -/
theorem pins_at {α : Type} {P : α → State → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins (fun a => At (P a) (f a)) [.esp] :=
  pins_esp f (fun _ _ h => h) hr

/-- `esp` is pinned in a branch. -/
theorem pins_at' {α : Type} {P : α → State → State → Prop} {X : α → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins (fun a s => At (P a) (f a) s ∧ X a s) [.esp] :=
  pins_esp (P := P) f (fun _ _ h => h.1) hr

/-- After the head: the tape's length against the width. -/
def DrawHead (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ t.cf = some (decide ((rInput s₀).rand.length - a.used < rWidth s₀))

/-- A complete draw. -/
def DrawFull (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ a.used + rWidth s₀ ≤ (rInput s₀).rand.length

/-- After the copy's header and first byte. -/
def CopyHead (a : DrawPub) (s₀ t : State) : Prop :=
  (∃ t₀, CopyInv s₀ t₀ (X86.arg s₀ 7 + BitVec.ofNat 32 a.used) (drawPlace s₀) (drawBytes s₀ a.used)
    (maskValue (rLead s₀).toNat) 1 t) ∧ t.zf = some (decide (rWidth s₀ - 1 = 0)) ∧
  (drawBytes s₀ a.used).length = rWidth s₀

/-- After the copy's header. -/
def CopyHdr (a : DrawPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.gpr .esi = X86.arg s₀ 7 + BitVec.ofNat 32 a.used ∧ t.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) ∧
    t.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (drawPlace s₀)

theorem copyInit_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) (.block copyInit) fun _ _ => True := by
  unfold copyInit
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun a => At (CopyHdr a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D, _⟩ => WP.mono (copyHeader_ok A D.smp.ready D.smp.usedW D.smp.width)
      fun u ⟨h, _, _, x, c, d⟩ => ⟨s₀, A, e, h, x, c, d⟩) ?_
  refine two_taint [.esp, .esi, .ecx, .edx] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, x₁, c₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, x₂, c₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  have esp := esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact esp
  · rw [x₁, x₂, pub_arg e 7 (by decide)]
  · rw [c₁, c₂, pub_rWidth e]
  · rw [d₁, d₂, esp]
    simp only [drawPlace, pub_qBytes e, pub_rWidth e]

theorem copy_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (two_post (Ψ := fun a => At (CopyHead a) a.pub) copyInit_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => ?_) ?_
  · have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := by
      simp only [drawBytes, List.length_take, List.length_drop]; omega
    exact WP.mono (copyInit_ok A D.smp.ready D.smp.usedW D.smp.width D.smp.mask hf (width_pos D.q))
      fun u ⟨I, z⟩ => ⟨s₀, A, e, ⟨t, I⟩, z, hdl⟩
  unfold copyRest
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, z₁, _⟩ ⟨s₂, _, e₂, _, z₂, _⟩ => by
    simp only [eval, z₁, z₂, pub_rWidth (e₁.trans e₂.symm)]) ?_ ?_
  · refine copyLoop_ct fun a t₁ t₂ h₁ h₂ r hr => ?_
    obtain ⟨⟨s₁, _, e₁, ⟨_, I₁⟩, _, l₁⟩, _⟩ := h₁
    obtain ⟨⟨s₂, _, e₂, ⟨_, I₂⟩, _, l₂⟩, _⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [I₁.esi, I₂.esi, pub_arg e 7 (by decide)]
    · rw [I₁.edx, I₂.edx, esp_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf)]
      simp only [drawPlace, pub_qBytes e, pub_rWidth e]
    · rw [I₁.ecx, I₂.ecx, l₁, l₂, pub_rWidth e]
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the copy. -/
structure Copied (a : DrawPub) (s₀ t : State) : Prop where
  pre : DrawPre a s₀ t
  full : a.used + rWidth s₀ ≤ (rInput s₀).rand.length
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- After consuming the draw. -/
structure Consumed (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : accepts s₀ (drawCand s₀ a.used) = a.acc
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- Before the comparison's loop. -/
def RangeHead (s₀ t : State) : Prop := ∃ t₀ cs, RangeInv s₀ t₀ cs (rWidth s₀) t

theorem inRange_ct : RelCT isa (Two fun a => At (Consumed a) a.pub) inRange fun _ _ => True := by
  unfold inRange
  refine RelCT.seq (two_piece (Ψ := fun a => At RangeHead a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (rangeInit_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q
      C.smp.width (copiedList_length _ _ _)) fun u ⟨I, _⟩ => ⟨s₀, A, e, t, _, I⟩) ?_
  refine rangeBody_ct fun a t₁ t₂ h₁ h₂ r hr => ?_
  obtain ⟨s₁, _, e₁, _, _, I₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, _, I₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [I₁.esi, I₂.esi, pub_rQ e, pub_qBytes e, pub_rWidth e]
  · rw [I₁.edx, I₂.edx, esp_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf)]
    simp only [drawPlace, pub_qBytes e, pub_rWidth e]
  · rw [I₁.ecx, I₂.ecx, pub_rWidth e]

/-- Before the decision. -/
structure Decided (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  zf : t.zf = some (!a.acc)

/-- After spending a draw. -/
def Spent (a : DrawPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some (decide (a.draws - 1 = 0))

theorem drawFinish_ct : RelCT isa (Two fun a => At (Decided a) a.pub) drawFinish fun _ _ => True := by
  unfold drawFinish
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩ => by simp only [eval, D₁.zf, D₂.zf]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
  refine RelCT.seq (two_piece (Ψ := fun a => At (Spent a) a.pub) [.esp]
    (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨⟨s₀, A, e, D⟩, _⟩ => WP.mono (drawDec_ok A D.smp D.pos D.le)
      fun u ⟨_, _, _, h, z, _⟩ => ⟨s₀, A, e, h, z⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.1) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the comparison, the decision: the draw's acceptance. -/
theorem inRange_decided {a : DrawPub} {s₀ t : State} (A : KeyABI s₀) (C : Consumed a s₀ t) :
    WP isa inRange t (Decided a s₀) :=
  WP.mono (inRange_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q C.smp.width (copiedList_length _ _ _)
    (width_pos C.q) fun i hi => by rw [copiedList_getD _ _ hi]; exact C.bytes i hi)
    fun u ⟨_, z, m, h, _⟩ => ⟨C.smp.congr A h (by rw [m]; exact Outs.refl _ _ _) (by rw [m]) (by rw [m]),
      C.pos, C.le, by rw [z, C.acc]⟩

theorem full_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub)
    (.seq copy (.seq (.block [.mov .eax (.mem (sp oUsed)), .alu .add .eax (.mem (sp oWidth)),
      .store (sp oUsed) .eax]) (.seq inRange drawFinish))) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a => At (Copied a) a.pub) copy_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => WP.mono (drawCopy_ok A D.smp hf (width_pos D.q))
      fun u ⟨S, hc, _, _⟩ => ⟨s₀, A, e, { D with smp := S }, hf, hc⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Consumed a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.pre.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (drawUsed_ok A C.pre.smp C.full)
      fun u ⟨S, hm, _⟩ => ⟨s₀, A, e, S, C.pre.pos, C.pre.le, C.pre.q, C.pre.acc C.full,
        drawUsed_bytes A hm C.bytes⟩) ?_
  exact RelCT.seq (two_post (Ψ := fun a => At (Decided a) a.pub) inRange_ct
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (inRange_decided A C) fun u D => ⟨s₀, A, e, D⟩) drawFinish_ct

theorem draw_ct : RelCT isa (Two fun a => At (DrawPre a) a.pub) draw fun _ _ => True := by
  unfold draw
  refine RelCT.seq (two_piece (Ψ := fun a => At (DrawHead a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D⟩ => WP.mono (drawHead_ok A D.smp)
      fun u ⟨S, _, _, c⟩ => ⟨s₀, A, e, { D with smp := S }, c⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, c₁⟩ ⟨s₂, _, e₂, _, c₂⟩ => by
    have e := e₁.trans e₂.symm
    simp only [eval, c₁, c₂, pub_randLen e, pub_rWidth e]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
  · refine two_map id (fun a t ⟨⟨s₀, A, e, D, c⟩, hb⟩ => ⟨s₀, A, e, D, ?_⟩) full_ct
    have := D.smp.usedBound
    show a.used + rWidth s₀ ≤ (rInput s₀).rand.length
    simp only [eval, c, Option.some.injEq, decide_eq_false_iff_not] at hb
    omega

end VG.Proof.Dsa.X86.KeyRandom
