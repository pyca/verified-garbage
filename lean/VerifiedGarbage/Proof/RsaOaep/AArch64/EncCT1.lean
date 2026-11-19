module

public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
meta import VerifiedGarbage.Proof.Mgf1.Basic
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaOaep.AArch64.EncCTBase`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on AArch64: two runs

As for decryption (`DecCTBase.lean`): two runs whose public data agree (the
pointers and lengths, `n`, `e` and `pre`'s words) have the same layout, and between the
frames' pushes and pops they are related by `PW`: each is `In` the frames
(`Ctx`, the pieces' `Rep` with our arguments in their slots) and satisfies
`X`, which fixes the registers the next piece's addresses and arguments
depend on as functions of the layout. A block that dereferences a pointer it
loads is split there (`pw_seq_tr`), the registers its second part
dereferences fixed by its first part (the `*E_pin` lemmas). The pieces
encryption shares with decryption relate two runs by `LR`, which `In`
implies (`pw_lr`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- `n`, `e` and the words of the buffers `X` (`pre`) agree in the two
runs' memories. -/
def LeakEq (L : ELay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat ∧
    ∀ R ∈ L.X, Spec.Rsa.wordsAt m₁ R.base (R.len / 8) = Spec.Rsa.wordsAt m₂ R.base (R.len / 8)

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : ELay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- `Ctx`, the pieces' `Rep` with our arguments in their slots, and `X` of
the frame's words and the state. -/
def In (L : ELay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (X : (Nat → BitVec 64) → State → Prop) (t : State) : Prop :=
  Ctx L g vv m₀ t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Slots L W ∧ X W t

/-- Two runs in the layout of `e`, with `P` bytes of stack for the calls,
each `In` the frames with `X`. -/
def PW (P : Nat) (e : Env) (X : (Nat → BitVec 64) → State → Prop) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = P ∧ LeakEq e.L e.m₁ e.m₂ ∧ In e.L e.g₁ e.v₁ e.m₁ X a ∧ In e.L e.g₂ e.v₂ e.m₂ X b

/-- What a piece establishes, by correctness. -/
abbrev PWStep (P : Nat) (e : Env) (c : Prog isa) (X X' : (Nat → BitVec 64) → State → Prop) : Prop :=
  ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = P → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
    Slots e.L W → X W t → WP isa c t (In e.L g vv m₀ X')

theorem pw_wp {P : Nat} {e : Env} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop}
    (hct : RelCT isa (PW P e X) c fun _ _ => True) (hw : PWStep P e c X X') :
    RelCT isa (PW P e X) c (PW P e X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, hk, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw _ _ _ s₁ _ _ hL hP c₁ R₁ S₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw _ _ _ s₂ _ _ hL hP c₂ R₂ S₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, hL, hP, hk, z₁, z₂⟩

/-- `pw_wp`, for a piece whose correctness needs `Q` of the entry memory,
which both runs' satisfy. -/
theorem pw_wpQ {P : Nat} {e : Env} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop} {Q : Mem → Prop}
    (q₁ : Q e.m₁) (q₂ : Q e.m₂) (hct : RelCT isa (PW P e X) c fun _ _ => True)
    (hw : ∀ g vv m₀ (t : State) V W, Q m₀ → e.L.Ok → e.L.P = P → Ctx e.L g vv m₀ t →
      Rep t.mem e.L.Q e.L.scr V W → Slots e.L W → X W t → WP isa c t (In e.L g vv m₀ X')) :
    RelCT isa (PW P e X) c (PW P e X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, hk, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw _ _ _ s₁ _ _ q₁ hL hP c₁ R₁ S₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw _ _ _ s₂ _ _ q₂ hL hP c₂ R₂ S₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, hL, hP, hk, z₁, z₂⟩

theorem pw_sp {P : Nat} {e : Env} {X : (Nat → BitVec 64) → State → Prop} {a b : State} (h : PW P e X a b) :
    a.sp = b.sp :=
  h.2.2.2.1.1.sp.trans h.2.2.2.2.1.sp.symm

/-- Code checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_taint {P : Nat} {e : Env} {c : Prog isa} {X : (Nat → BitVec 64) → State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ W₁ W₂ a b, X W₁ a → X W₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa (PW P e X) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ hp => by
    have hs := pw_sp hp
    obtain ⟨_, _, _, ⟨_, _, _, _, _, x₁⟩, ⟨_, _, _, _, _, x₂⟩⟩ := hp
    exact ⟨hs, fun r hr => hag _ _ _ _ x₁ x₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A block checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_blk {P : Nat} {e : Env} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ W₁ W₂ a b, X W₁ a → X W₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r) (hw : PWStep P e c X X') :
    RelCT isa (PW P e X) c (PW P e X') :=
  pw_wp (pw_taint rs h hag) hw

/-- Code whose second part `c₂` dereferences the registers `rs`, which its
first part `c₁` sets to `pin` in both runs. -/
theorem pw_seq_tr {P : Nat} {e : Env} {c₁ c₂ : Prog isa} {X : (Nat → BitVec 64) → State → Prop}
    (rs : List Reg) (pin : Reg → BitVec 64) {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) c₁ h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs rs) c₂ h₂).isSome = true)
    (hA : ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = P → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
      Slots e.L W → X W t → WP isa c₁ t fun u => u.sp = t.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) :
    RelCT isa (PW P e X) (.seq c₁ c₂) fun _ _ => True := by
  have h1 : RelCT isa (PW P e X) c₁ fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := by
    have hw := (RelCT.taint (A := taint) (P := PW P e X) (Taint.ofRegs []) (fun _ _ hp =>
      ⟨pw_sp hp, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) t₁).wpDep
      (F := fun (s u : State) => u.sp = s.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) fun s₁ s₂ hp => by
        obtain ⟨hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
        exact ⟨hA _ _ _ _ _ _ hL hP c₁ R₁ S₁ x₁, hA _ _ _ _ _ _ hL hP c₂ R₂ S₂ x₂⟩
    refine hw.mono (fun _ _ h => h) fun a b ⟨_, σ₁, σ₂, hσ, ⟨sa, ra⟩, ⟨sb, rb⟩⟩ =>
      ⟨by rw [sa, sb]; exact pw_sp hσ, fun r hr => (ra r hr).trans (rb r hr).symm⟩
  have h2 : RelCT isa (fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) c₂ fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨hs, hr⟩ =>
      ⟨hs, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) t₂
  exact h1.seq h2

/-- A piece shared with decryption, related by `LR` from what `In` gives. -/
theorem pw_lr {P : Nat} {e : Env} (hP16 : 16 ≤ e.L.P) {c : Prog isa} {X Y : (Nat → BitVec 64) → State → Prop}
    (hct : RelCT isa (LR e.L.Q e.L.scr Y) c fun _ _ => True)
    (hxy : ∀ g vv m₀ (t : State) W, e.L.Ok → Ctx e.L g vv m₀ t → Slots e.L W → X W t → Y W t) :
    RelCT isa (PW P e X) c fun _ _ => True :=
  hct.mono (fun _ _ ⟨hL, _, _, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ =>
    ⟨⟨V₁, W₁, c₁.lay hL hP16 R₁ S₁.scr, R₁, hxy _ _ _ _ _ hL c₁ S₁ x₁⟩,
      ⟨V₂, W₂, c₂.lay hL hP16 R₂ S₂.scr, R₂, hxy _ _ _ _ _ hL c₂ S₂ x₂⟩⟩) fun _ _ h => h

/-- `In`, from a piece's `Step` and `Rep`. -/
theorem In.of_step {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t u : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {ws : List Region} (S : Step L.Q L.scr ws t u)
    (hws : ∀ r ∈ ws, Region.Sub r L.OUT) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem L.Q L.scr V W)
    (hS : Slots L W) {X : (Nat → BitVec 64) → State → Prop} (hx : X W u) : In L g vv m₀ X u :=
  ⟨hc.step hL hP S hws, V, W, R, hS, hx⟩

/-! ## The loops' heads -/

section
variable {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
  (R : Rep u.mem F S V W)
include L

theorem clearE_pin :
    WP isa (.block (scr .x11 oEm ++ ([.movz .x .x12 128 0, .movz .x .x13 0 0] : List Instr))) u fun u' =>
      u'.sp = u.sp ∧ ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r =
        ([(Reg.x11, off S oEm), (.x12, BitVec.ofNat 64 128), (.x13, BitVec.ofNat 64 0)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = off S oEm ∧
      u'.gpr .x12 = BitVec.ofNat 64 128 ∧ u'.gpr .x13 = BitVec.ofNat 64 0) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, off S oEm), (.x12, BitVec.ofNat 64 128),
      (.x13, BitVec.ofNat 64 0)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, oEm, h96, L.sp, hs]
  oaep_fin

include R in
theorem seedE_pin {H : Hash} {sd : Addr} (hsd : W 29 = sd) (hD' : H.D ≤ 64) :
    WP isa (.block (([.ldrSp .x11 sSeed] : List Instr) ++ scr .x12 (oEm + 1) ++
      ([.movz .x .x13 (BitVec.ofNat 16 H.D) 0] : List Instr))) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r =
        ([(Reg.x11, sd), (.x12, off S (oEm + 1)), (.x13, BitVec.ofNat 64 H.D)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rsd := R.rd8 (d := 232) (k := 29) rfl (by decide) hsd
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = sd ∧
      u'.gpr .x12 = off S (oEm + 1) ∧ u'.gpr .x13 = BitVec.ofNat 64 H.D) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, sd), (.x12, off S (oEm + 1)),
      (.x13, BitVec.ofNat 64 H.D)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, sSeed, h96, h232, L.sp, hs, rsd,
    show oEm + 1 < 4096 by decide, imm16 (show H.D < 65536 by omega_using [hD'])]

theorem lhE_pin {H : Hash} (hD' : H.D ≤ 64) :
    WP isa (.block (scr .x11 oDig ++ scr .x12 (oEm + 1 + H.D) ++
      ([.movz .x .x13 (BitVec.ofNat 16 H.D) 0] : List Instr))) u fun u' => u'.sp = u.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r =
        ([(Reg.x11, off S oDig), (.x12, off S (oEm + 1 + H.D)), (.x13, BitVec.ofNat 64 H.D)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = off S oDig ∧
      u'.gpr .x12 = off S (oEm + 1 + H.D) ∧ u'.gpr .x13 = BitVec.ofNat 64 H.D) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, off S oDig), (.x12, off S (oEm + 1 + H.D)),
      (.x13, BitVec.ofNat 64 H.D)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, h96, L.sp, hs, show oDig < 4096 by decide,
    show oEm + 1 + H.D < 4096 by unfold oEm; omega_using [hD'], imm16 (show H.D < 65536 by omega_using [hD'])]

include R in
theorem msgE_pin {k mLen : Nat} {msg : Addr} (hk : W 21 = BitVec.ofNat 64 k) (hml : W 28 = BitVec.ofNat 64 mLen)
    (hmsg : W 27 = msg) (hkm : mLen + 1 ≤ k) :
    WP isa (.block (([.ldrSp .x11 sMsg] : List Instr) ++ scr .x12 oEm ++ ([.ldrSp .x10 sK, .add .x .x12 .x12 .x10,
      .ldrSp .x13 sMsgLen, .sub .x .x12 .x12 .x13, .subImm .x .x12 .x12 1] : List Instr))) u fun u' =>
      u'.sp = u.sp ∧ ∀ r ∈ [Reg.x11, .x12, .x13], u'.gpr r =
        ([(Reg.x11, msg), (.x12, off S (k - mLen - 1)), (.x13, BitVec.ofNat 64 mLen)].lookup r).getD 0 := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h216 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  have rml := R.rd8 (d := 224) (k := 28) rfl (by decide) hml
  have rmsg := R.rd8 (d := 216) (k := 27) rfl (by decide) hmsg
  have hsub : ∀ x y : BitVec 64, S + x - y = S + (x - y) := fun x y => by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have e1 : S + BitVec.ofNat 64 oEm + BitVec.ofNat 64 k - BitVec.ofNat 64 mLen - BitVec.ofNat 64 1 =
      off S (k - mLen - 1) := by
    rw [show oEm = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hsub, hsub,
      Offset.ofNat_sub_ofNat (by omega_using [hkm]), Offset.ofNat_sub_ofNat (by omega_using [hkm])]
  refine WP.mono (Q := fun (u' : State) => u'.sp = u.sp ∧ u'.gpr .x11 = msg ∧
      u'.gpr .x12 = off S (k - mLen - 1) ∧ u'.gpr .x13 = BitVec.ofNat 64 mLen) ?_
    fun u' ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, msg), (.x12, off S (k - mLen - 1)),
      (.x13, BitVec.ofNat 64 mLen)] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, sK, sMsgLen, sMsg, h96, h168, h216, h224, L.sp, hs, rk, rml, rmsg, e1,
    show oEm < 4096 by decide]

end

theorem zeroE_pin {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block [.ldrSp .x11 sOut, .ldrSp .x12 sK, .movz .x .x13 0 0]) t fun u => u.sp = t.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u.gpr r = (if r = .x11 then L.out else if r = .x12 then L.k else 0) := by
  have Ly := hc.lay hL hP R hS.scr
  have h152 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 152) 8 := Ly.ld (d := 152) (by decide)
  have h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) hS.out
  have rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  refine WP.mono (Q := fun (u : State) => u.sp = t.sp ∧ u.gpr .x11 = L.out ∧ u.gpr .x12 = L.k ∧ u.gpr .x13 = 0) ?_
    fun u ⟨hs, x11, x12, x13⟩ => ⟨hs, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> simp [x11, x12, x13]⟩
  oaep_run [sOut, sK, h152, h168, Ly.sp, ro, rk]
  and_intros <;> first | trivial | rfl

end VG.Proof.RsaOaep.AArch64.Enc

end

end

/-!
# RSAES-OAEP encryption on AArch64: `EM` and the call in constant time

`encMain` from two runs in the same layout (`encMain_tr`): the copies into
`EM` from the registers their heads fix (`*E_pin`), the label's hash (with
the table `hash`, which both runs hold) and MGF1 as for any caller (`pw_lr`), the arguments' blocks by the taint
analysis, and the call of a precomputed public operation, whose public
arguments, `pre`'s words and `e` agree in both runs (`pdCallCT`). Nothing
after the call branches on its result.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked pdCallCT)

/-- Two layouts' `pre` and tables from the two entry memories are the same. -/
theorem pre_eq {L : ELay} {m₁ m₂ : Mem} (q₁ : PreOk L m₁) (q₂ : PreOk L m₂) :
    preW L m₁ = preW L m₂ ∧ prlW L m₁ = prlW L m₂ ∧ tabW L m₁ = tabW L m₂ ∧ tabLW L m₁ = tabLW L m₂ := by
  obtain h := q₁.hx.symm.trans q₂.hx
  simp only [List.cons.injEq, PRE, TABJ, Sig.tableRegion, Region.mk.injEq, and_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact ⟨h1, BitVec.eq_of_toNat_eq (by omega_using [h2]), h4, h3⟩

/-- The registers of the call, with the first run's `pre`. -/
theorem readyP_of {L : ELay} {m m' : Mem} {t : State} (q : PreOk L m) (q' : PreOk L m') (h : PReadyP L m t) :
    PReadyP L m' t := by
  obtain ⟨w, wl, -⟩ := pre_eq q q'
  exact ⟨h.x0, h.x1, h.x2.trans w, h.x3.trans wl, h.x4, h.x5, h.x6, h.x7⟩

theorem putMsg_eq : putMsg = .seq (.block ((([.ldrSp .x11 sMsg] : List Instr) ++ scr .x12 oEm ++
    ([.ldrSp .x10 sK, .add .x .x12 .x12 .x10, .ldrSp .x13 sMsgLen, .sub .x .x12 .x12 .x13,
      .subImm .x .x12 .x12 1] : List Instr)) ++
    ([.movz .x .x10 1 0, .strb .x10 .x12 0, .addImm .x .x12 .x12 1] : List Instr)))
    (.ite (.nonzero .x .x13) copyLoop (.block [])) := rfl

variable {Hl : Hash} {Gm : Stream} (hH : StreamOK Hl.stream) (hG : StreamOK Gm) {f : Fns}

include hH hG in
theorem encMain_tr {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked)
    {P : Nat} {e : Env} (hL : e.L.Ok) (hP : c.stack ≤ e.L.P) (hP16 : 16 ≤ e.L.P) (hD : e.L.D = Hl.D)
    (q₁ : PreOk e.L e.m₁) (q₂ : PreOk e.L e.m₂) (hk : 2 * Hl.D + 2 + e.L.ml.toNat ≤ e.L.k.toNat)
    {p ai au af pL aiL auL afL : Addr} :
    RelCT isa (PW P e fun _ t => Table.TabX Gm f (arg 9) e.L.Q e.L.scr p ai au af t ∧
        Table.TabX Hl.stream f (arg 8) e.L.Q e.L.scr pL aiL auL afL t)
      (Impl.RsaOaep.AArch64.Precomputed.encMain Hl f c.name c.code) fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  obtain hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  obtain f4 : MFit 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  obtain f2 : MFit (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  obtain ly : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → Slots e.L W →
      Lay t e.L.Q e.L.scr := fun hc R hS => hc.lay hL hP16 R hS.scr
  obtain hk3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 21 = BitVec.ofNat 64 e.L.k.toNat := fun hS => by
    rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain hm3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 28 = BitVec.ofNat 64 e.L.ml.toNat := fun hS => by
    rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The seed's and the message's bytes are apart from our working space.
  obtain hsdS : ∀ i < Hl.D, ∀ j < oRsa, off e.L.sd i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.sd + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_SD e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega_arith)
        (by have := hL.bR _ (ro_SD e.L); simp only at this; omega_arith))
  obtain hmsS : ∀ i < e.L.ml.toNat, ∀ j < oRsa, off e.L.msg i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.msg + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_MSG e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base e.L.msg (d := i) (n := 1) (k := e.L.ml.toNat) (by omega_arith)
        (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega_arith))
  obtain inRd : ∀ {g vv m₀} {u : State} {R : Region}, Ctx e.L g vv m₀ u →
      R ∈ [e.L.N, e.L.E, e.L.LAB, e.L.MSG, e.L.SD] ++ e.L.X ++ [e.L.ARGS] →
      ∀ {a : Addr} {n : Nat}, R.Contains a n → InRegions (u.rd ++ u.wr) a n := fun hcu hR _ _ h3 =>
    ⟨_, List.mem_append_left _ (by rw [hcu.rd]; exact hR), h3⟩
  let TX : (Nat → BitVec 64) → State → Prop := fun _ t => Table.TabX Gm f (arg 9) e.L.Q e.L.scr p ai au af t
  let TX2 : (Nat → BitVec 64) → State → Prop := fun W t => TX W t ∧
    Table.TabX Hl.stream f (arg 8) e.L.Q e.L.scr pL aiL auL afL t
  simp only [Impl.RsaOaep.AArch64.Precomputed.encMain, encEm, seqs]
  -- `EM`'s place cleared.
  refine RelCT.seq (R := PW P e TX) (RelCT.seq (pw_wp (X' := TX2) (pw_seq_tr [.x11, .x12, .x13]
      (fun r => ([(Reg.x11, off e.L.scr oEm), (.x12, BitVec.ofNat 64 128), (.x13, BitVec.ofNat 64 0)].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => clearE_pin (ly hc R hS))
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (clearEm_ok (ly hc R hS) R))
      fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS ⟨hx.1.step Su sy, hx.2.step Su sy⟩) ?_) ?_
  -- The seed.
  · refine RelCT.seq (pw_wp (X' := TX2) (pw_seq_tr [.x11, .x12, .x13]
        (fun r => ([(Reg.x11, e.L.sd), (.x12, off e.L.scr (oEm + 1)), (.x13, BitVec.ofNat 64 Hl.D)].lookup r).getD 0)
        (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (([.ldrSp .x11 sSeed] : List Instr) ++
          scr .x12 (oEm + 1) ++ ([.movz .x .x13 (BitVec.ofNat 16 gH.D) 0] : List Instr))) (by rfl) (by taint_decide))
        (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => seedE_pin (ly hc R hS) R hS.sd hD64)
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (copySeed_ok (ly hc R hS) R (H := Hl) hS.sd hD0 hD64
        (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega_arith)
          (by have := hL.bR _ (ro_SD e.L); simp only at this; omega_arith)))
        (fun i hi j hj => hsdS i hi _ (by unfold oEm; omega_arith))))
        fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS ⟨hx.1.step Su sy, hx.2.step Su sy⟩) ?_
    -- The table's address to its slot.
    refine RelCT.seq (pw_blk (X' := fun W t => TX2 W t ∧ W 32 = pL) [] (by taint_decide) nopin
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (tabSlot_ok (by decide) (ly hc R hS) R hx.2.1))
        fun _ ⟨⟨_, Su, Ru, _⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru
          (hS.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)])
          ⟨⟨hx.1.step Su sy, hx.2.step Su sy⟩, by simp [upd]⟩) ?_
    -- The label's hash.
    refine RelCT.seq (pw_wp (X' := TX)
      (pw_lr hP16 (hashLabelT_tr hH e.L.labl.isLt (.inl rfl) (f := f) (p := pL) (ai := aiL) (au := auL) (af := afL))
        fun _ _ _ _ _ _ hc hS hx => ⟨hc.labAt hL hP16 hS, hx.2,
          ⟨⟨_, _, hx.1.2.1, Step.refl _ _ _ _, rfl⟩, hx.1.2.2.1, hx.1.2.2.2.1, hx.1.2.2.2.2⟩⟩)
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (hashLabelT_ok hH (Hs := Hs) hHh hx.1.2.1 (ly hc R hS) R
        hx.2 (hc.labAt hL hP16 hS) (o := oDig) (.inl rfl)))
        fun _ ⟨⟨_, Su, _, Ru, _, _⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS (hx.1.1.step Su sy)) ?_
    -- `lHash` after the seed.
    refine RelCT.seq (pw_wp (X' := TX) (pw_seq_tr [.x11, .x12, .x13]
        (fun r => ([(Reg.x11, off e.L.scr oDig), (.x12, off e.L.scr (oEm + 1 + Hl.D)),
          (.x13, BitVec.ofNat 64 Hl.D)].lookup r).getD 0)
        (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (scr .x11 oDig ++ scr .x12 (oEm + 1 + gH.D) ++
          ([.movz .x .x13 (BitVec.ofNat 16 gH.D) 0] : List Instr))) (by rfl) (by taint_decide))
        (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => lhE_pin (ly hc R hS) hD64)
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (copyLh_ok (ly hc R hS) R (H := Hl) hD0 hD64))
        fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS (hx.step Su sy)) ?_
    -- `0x01` and the message.
    refine pw_wp (X' := TX) (by
        rw [putMsg_eq]
        exact RelCT.seq_block_append (pw_seq_tr [.x11, .x12, .x13]
          (fun r => ([(Reg.x11, e.L.msg), (.x12, off e.L.scr (e.L.k.toNat - e.L.ml.toNat - 1)),
            (.x13, BitVec.ofNat 64 e.L.ml.toNat)].lookup r).getD 0)
          (by taint_decide) (by taint_decide)
          fun _ _ _ _ _ _ _ _ hc R hS _ => msgE_pin (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg (by omega_arith)))
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (putMsg_ok (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg
        (by omega_arith) hk1024 (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.msg (d := i) (n := 1)
          (k := e.L.ml.toNat) (by omega_arith) (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega_arith)))
        hmsS))
        fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS (hx.step Su sy)
  -- `DB` masked.
  refine RelCT.seq (pw_blk (X' := fun W t => MArgs W e.L.scr 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) ∧ TX W t) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (dbArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (dbArgs_ok (ly hc R hS) R (hk3 hS) (by omega_arith)
      (by omega_arith) hk1024 []))
      fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)) ⟨mW_args _ _ _ _ _ _, hx.step Su sy⟩) ?_
  refine RelCT.seq (pw_wp (X' := TX) (pw_lr hP16 (Table.mgfXorT_tr hG (by decide) f4
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) (by taint_decide))
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (Table.mgfXorT_ok hG hGh hGl hGv (by decide) hx.2.1
      (ly hc R hS) R f4 hx.1))
      fun _ ⟨⟨_, Su, _, W', Ru, hW', _⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith)) (hx.2.step Su sy)) ?_
  -- The seed masked.
  refine RelCT.seq (pw_blk (X' := fun W t => MArgs W e.L.scr (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D ∧ TX W t) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (seedArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (seedArgs_ok (ly hc R hS) R (hk3 hS) (by omega_arith)
      (by omega_arith) hk1024 []))
      fun _ ⟨⟨_, Su, Ru⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)) ⟨mW_args _ _ _ _ _ _, hx.step Su sy⟩) ?_
  refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_lr hP16 (Table.mgfXorT_tr hG (by decide) f2
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) (by taint_decide))
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.mgfXorT_ok hG hGh hGl hGv (by decide) hx.2.1 (ly hc R hS) R f2
      hx.1)
      fun _ ⟨_, Su, _, W', Ru, hW', _⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith)) trivial) ?_
  -- The call.
  refine RelCT.seq (pw_wpQ (X' := fun W t => PReadyP e.L e.m₁ t ∧ CallArgs e.L W) (Q := PreOk e.L) q₁ q₂
    (pw_taint [] (by taint_decide) nopin) fun _ _ _ t V W hq _ _ hc R hS _ => ?_) ?_
  · have hS10 : Slots e.L (pubW e.L W) := hS.of fun j h1 _ _ => by
      simp only [pubW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
    rw [Impl.RsaOaep.AArch64.Precomputed.pubArgs, pubArgs_eq, WP.block_append_iff, WP.block_append_iff]
    exact WP.mono (pubW_ok hL hP16 hc R hS) fun _ ⟨hc10, R10⟩ =>
      WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun _ ⟨hc11, hm11, hr11⟩ =>
        WP.mono (loads_ok hL hP16 hc11 hq hr11) fun _ ⟨hc12, hm12, hr12⟩ =>
          ⟨hc12, V, _, hm12 ▸ hm11 ▸ R10, hS10, readyP_of hq q₁ hr12, ⟨by simp [pubW, upd], by simp [pubW, upd]⟩⟩
  refine pdCallCT c fun t₁ t₂ ⟨_, _, hl, ⟨c₁, _, _, R₁, _, r₁, A₁⟩, ⟨c₂, _, _, R₂, _, r₂, A₂⟩⟩ => ?_
  obtain r₂' := readyP_of q₁ q₂ r₂
  obtain ⟨w, wl, -⟩ := pre_eq q₁ q₂
  obtain sa : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → CallArgs e.L W →
      stackArg t 0 = e.L.scr + BitVec.ofNat 64 8192 ∧ stackArg t 1 = e.L.sl - BitVec.ofNat 64 1024 :=
    fun hc R hA => ⟨by rw [stackArg, stackArgAddr, hc.sp]; exact (R.fr 0 (by unfold nW frameBytes; omega_arith)).trans hA.s0,
      by rw [stackArg, stackArgAddr, hc.sp]; exact (R.fr 1 (by unfold nW frameBytes; omega_arith)).trans hA.s1⟩
  refine ⟨pd_ok hL hP c₁ q₁ r₁ R₁ A₁, pd_ok hL hP c₂ q₂ r₂' R₂ A₂,
    ⟨c₁.sp.trans c₂.sp.symm, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [r₁.x0.trans r₂.x0.symm, r₁.x1.trans r₂.x1.symm, r₁.x2.trans r₂.x2.symm, r₁.x3.trans r₂.x3.symm,
      r₁.x4.trans r₂.x4.symm, r₁.x5.trans r₂.x5.symm, r₁.x6.trans r₂.x6.symm, r₁.x7.trans r₂.x7.symm]
  · rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl
    · rw [(sa c₁ R₁ A₁).1, (sa c₂ R₂ A₂).1]
    · rw [(sa c₁ R₁ A₁).2, (sa c₂ R₂ A₂).2]
  · have hx := hl.2.2 (PRE e.L e.m₁) (by rw [q₁.hx]; simp)
    simp only [Nat.mul_div_cancel _ (by decide : 0 < 8)] at hx
    rw [r₁.x2, r₁.x3, r₂'.x2, r₂'.x3, pre_words hL c₁ q₁, pre_words hL c₂ q₂, ← w, ← wl, hx]
  · rw [r₁.x4, r₁.x5, r₂.x4, r₂.x5]
    obtain b₁ := c₁.bytes_ro hL (ro_E e.L)
    obtain b₂ := c₂.bytes_ro hL (ro_E e.L)
    simp only at b₁ b₂
    rw [b₁, b₂, hl.2.1]

end VG.Proof.RsaOaep.AArch64.Enc
