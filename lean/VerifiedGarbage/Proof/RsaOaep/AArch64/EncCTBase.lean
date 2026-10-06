import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT

/-!
# RSAES-OAEP encryption on AArch64: two runs

As for decryption (`DecCTBase.lean`): two runs whose public data agree (the
pointers and lengths, `n` and `e`) have the same layout, and between the
frames' pushes and pops they are related by `PW`: each is `In` the frames
(`Ctx`, the pieces' `Rep` with our arguments in their slots) and satisfies
`X`, which fixes the registers the next piece's addresses and arguments
depend on as functions of the layout. A block that dereferences a pointer it
loads is split there (`pw_seq_tr`), the registers its second part
dereferences fixed by its first part (the `*E_pin` lemmas). The pieces
encryption shares with decryption relate two runs by `LR`, which `In`
implies (`pw_lr`).
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- `n` and `e` agree in the two runs' memories. -/
def LeakEq (L : ELay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat

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
theorem pw_lr {P : Nat} (hP16 : 16 ≤ P) {e : Env} {c : Prog isa} {X Y : (Nat → BitVec 64) → State → Prop}
    (hct : RelCT isa (LR e.L.Q e.L.scr Y) c fun _ _ => True)
    (hxy : ∀ g vv m₀ (t : State) W, e.L.Ok → Ctx e.L g vv m₀ t → Slots e.L W → X W t → Y W t) :
    RelCT isa (PW P e X) c fun _ _ => True :=
  hct.mono (fun _ _ ⟨hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ =>
    ⟨⟨V₁, W₁, c₁.lay hL (hP ▸ hP16) R₁ S₁.scr, R₁, hxy _ _ _ _ _ hL c₁ S₁ x₁⟩,
      ⟨V₂, W₂, c₂.lay hL (hP ▸ hP16) R₂ S₂.scr, R₂, hxy _ _ _ _ _ hL c₂ S₂ x₂⟩⟩) fun _ _ h => h

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
    show oEm + 1 < 4096 by decide, imm16 (show H.D < 65536 by omega)]

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
    show oEm + 1 + H.D < 4096 by unfold oEm; omega, imm16 (show H.D < 65536 by omega)]

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
      Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega)]
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
