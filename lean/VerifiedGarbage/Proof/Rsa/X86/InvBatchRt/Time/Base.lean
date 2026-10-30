module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.X86.State

/-! # Constant time of the batched inverse, one operation at a time

The constant-time analysis forgets the public words of the working space at a
store of a secret through a pointer it cannot place, as every array loop does,
while the code reads the arrays' addresses and the count from the header's
slots before every operation. So each operation is checked on its own
(`leaf`), from states whose slots agree because both runs satisfy `Bx` (the
slots hold addresses and lengths that depend only on the working space and the
modulus's length), in a view of the state with the working space as its only
writable region; the operations are joined by `RelCT.seq`, with `Bx` carried
through each by its correctness lemma.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass.X86.Inv (wordClob)

/-- The bytes of the return address and the arguments the operations may read: those up to
the working space's length, the argument after the working space's (`L.ws`). -/
def argBytes (L : Lay) : Nat := 4 + 4 * (L.ws + 2)

/-- The return address and those arguments lie apart from every writable region. -/
def ArgsOk (L : Lay) (s : State) : Prop :=
  (s.gpr .esp).toNat + argBytes L ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argBytes L⟩ r

/-- The call's public data: those arguments, and the stack pointer. -/
structure Public (L : Lay) (args : Nat → BitVec 32) (base : Addr) (size : Nat) (sp : BitVec 32) (s : State) :
    Prop where
  argsOk : ArgsOk L s
  stack : s.gpr .esp = sp
  arguments : ∀ i, i < L.ws + 2 → VG.Proof.Bignum.X86.CallArgument s base size i (args i)

theorem Public.keep {L : Lay} {args : Nat → BitVec 32} {base : Addr} {size : Nat} {sp : BitVec 32} {s t : State}
    {regs : List Reg} (h : Public L args base size sp s) (K : Keeps regs s t) (keepSp : .esp ∉ regs)
    (O : Outside base 0 size s.mem t.mem) : Public L args base size sp t := by
  have esp := K.1 .esp keepSp
  refine ⟨⟨?_, ?_⟩, esp.trans h.stack, fun i hi => (h.arguments i hi).keep K keepSp O⟩
  · rw [esp]; exact h.argsOk.1
  · intro r hr
    rw [esp]
    exact h.argsOk.2 r (K.2.2 ▸ hr)

/-- What each operation's check starts from: `edi` the working space, the slots and the count
public, the arguments public, the workspace's address the argument `L.ws`. -/
def τS (L : Lay) : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false, lens := [160], bases := [(.edi, 0, 0)],
    slots := VG.Slots.ofList [(0, 52, 48)], argLen := argBytes L, argBases := [(4 + 4 * L.ws, 0)] }

/-- The state with every region readable and only the working space writable. -/
def view (s : State) (B : Addr) (Z : Nat) : State := s.withRegions (s.rd ++ s.wr) [⟨B, Z⟩]

theorem lift_exec {s z : State} {B : Addr} {Z : Nat} {c : Prog isa} {tr : List Leak}
    (hs : (⟨B, Z⟩ : Region) ∈ s.wr) (he : Exec isa c (view s B Z) tr z) :
    Exec isa c s tr (z.withRegions s.rd s.wr) := by
  have cw : Covers (view s B Z).wr s.wr := by
    apply Covers.of_mem
    intro r hr
    simp only [view, State.withRegions_wr, List.mem_singleton] at hr
    subst r
    exact hs
  have cr : Covers ((view s B Z).rd ++ (view s B Z).wr) (s.rd ++ s.wr) := by
    simp only [view, State.withRegions_rd]
    exact Covers.append_left (Covers.refl _) (cw.trans (Covers.of_mem fun r hr => List.mem_append_right _ hr))
  have E := VG.X86.Exec.widen he cr cw
  simpa only [view, State.withRegions_withRegions, State.withRegions_self] using E

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem callArg_view {s : State} {i : Nat} {v : BitVec 32}
    (h : VG.Proof.Bignum.X86.CallArgument s B Z i v) : VG.Proof.Bignum.X86.CallArgument (view s B Z) B Z i v := by
  obtain ⟨r, hr, hc⟩ := h.stack.read
  exact ⟨⟨⟨r, by simp only [view, State.withRegions_rd, State.withRegions_wr]; exact List.mem_append_left _ hr, hc⟩,
    h.stack.apart⟩, h.value⟩

theorem RtWs.view {s : State} (h : RtWs L s B Z len N) : RtWs L (view s B Z) B Z len N := by
  obtain ⟨⟨⟨edi, _, nw, stk⟩, fits, wpos, wle⟩, lenArg, wsArg, lenLe, layLen⟩ := h
  exact ⟨⟨⟨edi, List.mem_singleton_self _, nw, stk⟩, fits, wpos, wle⟩,
    lenArg.imp fun _ ⟨l, e, c⟩ => ⟨l, e, callArg_view c⟩, callArg_view wsArg, lenLe, layLen⟩

theorem Bx.view {s : State} (h : Bx L s B Z len N) : Bx L (view s B Z) B Z len N :=
  ⟨RtWs.view h.ws, h.slots, h.room⟩

/-- Both runs hold the same slot words: the arrays' addresses and the half count. -/
theorem slot_words {s t : State} (hs : Bx L s B Z len N) (ht : Bx L t B Z len N) :
    ∀ q < 12, w32 s.mem B (52 + 4 * q) = w32 t.mem B (52 + 4 * q) := by
  intro q hq
  rcases Nat.lt_or_ge q 11 with h | h
  · have e : ∀ q < 11, slot (cached.getD q 0) = some (52 + 4 * q) := by decide
    rw [hs.slots.addr _ _ (e q h), ht.slots.addr _ _ (e q h)]
  · have e : 52 + 4 * q = halfSlot := by simp only [halfSlot]; omega
    rw [e, hs.slots.half, ht.slots.half]

/-- The runs a leaf starts from: the context, and the call's public data, in both. -/
structure Rel (L : Lay) (B : Addr) (Z len N : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s t : State) : Prop where
  bs : Bx L s B Z len N
  bt : Bx L t B Z len N
  ps : Public L args B Z sp s
  pt : Public L args B Z sp t

/-- The view is well formed for the analysis: `edi` and the argument `L.ws` the working space. -/
theorem wfS {u : State} {args : Nat → BitVec 32} {sp : BitVec 32} (hu : RtWs L u B Z len N)
    (hz : 160 ≤ Z) (pu : Public L args B Z sp u) : VG.X86.Taint.Wf (τS L) (view u B Z) := by
  have hn := hu.ws.workspace.nowrap
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨List.Forall₂.cons (show 160 ≤ Z by omega) List.Forall₂.nil,
    List.pairwise_singleton _ _, fun r hr => by
      cases hr with
      | head => exact hn
      | tail _ h => cases h⟩, ?_, ?_,
    fun _ => ⟨pu.argsOk.1, fun r hr => by
      simp only [view, State.withRegions_wr, List.mem_singleton] at hr; subst r
      exact pu.argsOk.2 _ hu.ws.workspace.wr⟩, ?_⟩
  · intro p hp
    simp only [τS, List.mem_singleton] at hp
    subst p
    show addr (u.gpr .edi) 0 = B
    simpa only [addr, BitVec.add_zero] using hu.ws.workspace.edi
  · intro p hp; cases hp
  · intro p hp
    simp only [τS, List.mem_singleton] at hp
    subst p
    refine ⟨by simp only [τS, argBytes]; omega, ?_⟩
    have v := hu.wsArg.value
    change u.mem.readW (addr (u.gpr .esp) (4 + 4 * L.ws)) 32 = _ at v
    show addr (u.mem.readW (addr (u.gpr .esp) (4 + 4 * L.ws)) 32) 0 = B
    rw [v]
    simp only [addr, BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := B.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem agreeS {s t : State} {args : Nat → BitVec 32} {sp : BitVec 32}
    (h : Rel L B Z len N args sp s t) : VG.X86.Taint.Agree (τS L) (view s B Z) (view t B Z) := by
  have hn := h.bs.nowrap
  have hf := h.bs.fits
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset] at hf
  have wf : ∀ {u : State}, Bx L u B Z len N → Public L args B Z sp u → VG.X86.Taint.Wf (τS L) (view u B Z) :=
    fun hu pu => wfS hu.ws (by omega) pu
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => rfl, wf h.bs h.ps, wf h.bt h.pt,
    VG.X86.Taint.slotsOk_of_list rfl (fun sl hsl => by
      simp only [List.mem_singleton] at hsl; subst hsl; change 52 + 48 ≤ ([160] : List Nat).getD 0 0; decide), ?_, fun _ => h.ps.stack.trans h.pt.stack.symm, ?_⟩
  · intro r hr
    simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.bs.ws.ws.workspace.edi_toNat.trans h.bt.ws.ws.workspace.edi_toNat.symm)
    · exact h.ps.stack.trans h.pt.stack.symm
  · intro i k hk
    simp only [τS, VG.Slots.has_ofList, List.mem_singleton] at hk
    obtain ⟨_, rfl, rfl, h₁, h₂⟩ := hk
    simp only at h₁ h₂
    change s.mem (B + BitVec.ofNat 64 k) = t.mem (B + BitVec.ofNat 64 k)
    have W := slot_words h.bs h.bt ((k - 52) / 4) (by omega)
    have e : B + BitVec.ofNat 64 k = off B (52 + 4 * ((k - 52) / 4)) + BitVec.ofNat 64 ((k - 52) % 4) := by
      simp only [off]; rw [VG.Offset.add_add]; congr 2; omega
    rw [e, Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (BitVec.eq_of_toNat_eq W)
  · intro k h4 hk
    simp only [τS] at hk
    change s.mem (VG.X86.Taint.argByte s (VG.X86.Taint.depth (τS L).stk + k)) =
      t.mem (VG.X86.Taint.argByte t (VG.X86.Taint.depth (τS L).stk + k))
    rw [show VG.X86.Taint.depth (τS L).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq h.ps.argsOk.1 h4 hk, VG.X86.Taint.argByte_eq h.pt.argsOk.1 h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ ((h.ps.arguments _ (by simp only [argBytes] at hk; omega)).value.trans
      (h.pt.arguments _ (by simp only [argBytes] at hk; omega)).value.symm)

/-- An operation the taint analysis checks on the views of two runs leaks the same trace in
both: each view runs it (by the operation's correctness), and its run is the state's, widened. -/
theorem leaf {P : State → State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hp : ∀ s t, P s t → VG.X86.Taint.Agree τ (view s B Z) (view t B Z))
    (hw : ∀ s t, P s t → (⟨B, Z⟩ : Region) ∈ s.wr ∧ (⟨B, Z⟩ : Region) ∈ t.wr)
    (hv : ∀ s t, P s t → (∃ tr z, Exec isa c (view s B Z) tr z) ∧ ∃ tr z, Exec isa c (view t B Z) tr z)
    (h : (VG.Taint.check sseTaint τ c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨⟨tr₁, z₁, v₁⟩, ⟨tr₂, z₂, v₂⟩⟩ := hv _ _ hP
  obtain ⟨w₁, w₂⟩ := hw _ _ hP
  have T := RelCT.taint (A := sseTaint) (P := fun a b => a = view s₁ B Z ∧ b = view s₂ B Z) τ
    (fun _ _ ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ hp _ _ hP) h _ _ _ _ _ _ ⟨rfl, rfl⟩ v₁ v₂
  refine ⟨?_, trivial⟩
  rw [← (Exec.det (lift_exec w₁ v₁) e₁).1, ← (Exec.det (lift_exec w₂ v₂) e₂).1]
  exact T.1

theorem Public.view {args : Nat → BitVec 32} {sp : BitVec 32} {s : State} (h : Public L args B Z sp s)
    (hb : (⟨B, Z⟩ : Region) ∈ s.wr) : Public L args B Z sp (view s B Z) := by
  refine ⟨⟨h.argsOk.1, fun r hr => ?_⟩, h.stack, fun i hi => callArg_view (h.arguments i hi)⟩
  cases hr with
  | head => exact h.argsOk.2 _ hb
  | tail _ h => cases h

/-- What an operation starts from in each run: the context, the call's public data, and facts `E`
about the registers and memory, which hold of the view too. -/
def Pre (L : Lay) (B : Addr) (Z len N : Nat) (args : Nat → BitVec 32) (sp : BitVec 32)
    (E : (Reg → BitVec 32) → Mem → Prop) (s : State) : Prop :=
  Bx L s B Z len N ∧ Public L args B Z sp s ∧ E s.gpr s.mem

theorem Pre.view {args : Nat → BitVec 32} {sp : BitVec 32} {E : (Reg → BitVec 32) → Mem → Prop} {s : State}
    (h : Pre L B Z len N args sp E s) : Pre L B Z len N args sp E (view s B Z) :=
  ⟨Bx.view h.1, Public.view h.2.1 h.1.ws.ws.workspace.wr, h.2.2⟩

/-- An operation that the analysis checks from `τS`, run from `Pre`: each run satisfies what the
operation's correctness says of it. -/
theorem leafU {args : Nat → BitVec 32} {sp : BitVec 32} {E : (Reg → BitVec 32) → Mem → Prop}
    {Q : State → Prop} {c : Prog isa}
    (hf : ∀ s, Pre L B Z len N args sp E s → WP isa c s Q) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) c hc).isSome = true) :
    RelCT isa (fun s t => Pre L B Z len N args sp E s ∧ Pre L B Z len N args sp E t) c
      (fun s t => Q s ∧ Q t) := by
  have ex : ∀ s, Pre L B Z len N args sp E s → ∃ tr z, Exec isa c (view s B Z) tr z := fun s ps =>
    let ⟨tr, z, e, _⟩ := hf _ ps.view
    ⟨tr, z, e⟩
  have R := leaf (P := fun s t => Pre L B Z len N args sp E s ∧ Pre L B Z len N args sp E t) (τS L)
    (fun _ _ ⟨ps, pt⟩ => agreeS ⟨ps.1, pt.1, ps.2.1, pt.2.1⟩)
    (fun _ _ ⟨ps, pt⟩ => ⟨ps.1.ws.ws.workspace.wr, pt.1.ws.ws.workspace.wr⟩)
    (fun _ _ ⟨ps, pt⟩ => ⟨ex _ ps, ex _ pt⟩) h
  exact (RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf s ps, hf t pt⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

/-! ## Before the slots -/

/-- `τS` before the slots are written. -/
def τ0 (L : Lay) : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false, lens := [160], bases := [(.edi, 0, 0)],
    argLen := argBytes L, argBases := [(4 + 4 * L.ws, 0)] }

/-- The runs' start: the working space before its slots, and the call's public data. -/
def Pre0 (L : Lay) (B : Addr) (Z len N : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  RtWs L s B Z len N ∧ 16 ≤ N ∧ Public L args B Z sp s

theorem agree0 {s t : State} {args : Nat → BitVec 32} {sp : BitVec 32}
    (hs : Pre0 L B Z len N args sp s) (ht : Pre0 L B Z len N args sp t) :
    VG.X86.Taint.Agree (τ0 L) (view s B Z) (view t B Z) := by
  have hf : VG.Impl.Rsa.X86.Keys.hdr + N * VG.Proof.Rsa.X86.Keys.S (kw len) ≤ Z := hs.1.ws.fits
  rw [show VG.Impl.Rsa.X86.Keys.hdr = 160 from rfl] at hf
  have wf : ∀ {u : State}, Pre0 L B Z len N args sp u → VG.X86.Taint.Wf (τ0 L) (view u B Z) := fun hu =>
    let w := wfS hu.1 (by omega) hu.2.2
    ⟨w.lens, w.bases, w.wbases, w.args, w.argBases, w.stk, w.frames, w.room⟩
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => rfl, wf hs, wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => hs.2.2.stack.trans ht.2.2.stack.symm, ?_⟩
  · intro r hr
    simp only [τ0, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.ws.workspace.edi_toNat.trans ht.1.ws.workspace.edi_toNat.symm)
    · exact hs.2.2.stack.trans ht.2.2.stack.symm
  · intro k h4 hk
    simp only [τ0] at hk
    change s.mem (VG.X86.Taint.argByte s (VG.X86.Taint.depth (τ0 L).stk + k)) =
      t.mem (VG.X86.Taint.argByte t (VG.X86.Taint.depth (τ0 L).stk + k))
    rw [show VG.X86.Taint.depth (τ0 L).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq hs.2.2.argsOk.1 h4 hk, VG.X86.Taint.argByte_eq ht.2.2.argsOk.1 h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ ((hs.2.2.arguments _ (by simp only [argBytes] at hk; omega)).value.trans
      (ht.2.2.arguments _ (by simp only [argBytes] at hk; omega)).value.symm)

theorem Pre0.view {args : Nat → BitVec 32} {sp : BitVec 32} {s : State} (h : Pre0 L B Z len N args sp s) :
    Pre0 L B Z len N args sp (view s B Z) :=
  ⟨RtWs.view h.1, h.2.1, Public.view h.2.2 h.1.ws.workspace.wr⟩

/-- `leafU` from `Pre0`, checked from `τ0`. -/
theorem leaf0 {args : Nat → BitVec 32} {sp : BitVec 32} {Q : State → Prop} {c : Prog isa}
    (hf : ∀ s, Pre0 L B Z len N args sp s → WP isa c s Q) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τ0 L) c hc).isSome = true) :
    RelCT isa (fun s t => Pre0 L B Z len N args sp s ∧ Pre0 L B Z len N args sp t) c (fun s t => Q s ∧ Q t) := by
  have ex : ∀ s, Pre0 L B Z len N args sp s → ∃ tr z, Exec isa c (view s B Z) tr z := fun s ps =>
    let ⟨tr, z, e, _⟩ := hf _ ps.view
    ⟨tr, z, e⟩
  have R := leaf (P := fun s t => Pre0 L B Z len N args sp s ∧ Pre0 L B Z len N args sp t) (τ0 L)
    (fun _ _ ⟨ps, pt⟩ => agree0 ps pt)
    (fun _ _ ⟨ps, pt⟩ => ⟨ps.1.ws.workspace.wr, pt.1.ws.workspace.wr⟩)
    (fun _ _ ⟨ps, pt⟩ => ⟨ex _ ps, ex _ pt⟩) h
  exact (RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf s ps, hf t pt⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

end VG.Proof.Rsa.X86.InvBatchRt.Time
