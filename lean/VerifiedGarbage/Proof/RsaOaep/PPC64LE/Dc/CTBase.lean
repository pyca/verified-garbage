module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Pre

/-!
# RSAES-OAEP decryption on PPC64LE: two runs

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, the first run's entry state: `PubD a s` says the entry state
`s` has `a`'s public data (`pubD_of`, from the shared contract's). After the
private operation, `DX a t` says `t` has `Base` for the decoding from such an
entry state, whose working space and `k`, `out`, `msg_len` and the label in
`r14`–`r19` are then `a`'s (`DX.pins`), while `r20` holds that run's own
result. The shared code compares runs whose `Base` has the same functions
of the base state: the working space at `stackArg x 13` (`SX`) and the
values of `r15`–`r23` read from `x`, with the result in its `r0` (`VX`); the
base state of a run is its entry state with the memory after the private
operation and the result in `r0` (`bx`, `toX`), for which the stack pointer
and `S` are public data (`okX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Pins)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The shared contract's public data, by name. -/
structure PubD (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 15, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r6) (a.gpr .r7).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat

theorem pubD_of {H G : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaOaep.decryptContract H G abi stackBytes).pub s₁ s₂) : PubD s₁ s₂ := by
  have e : stackBytes = 3775 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h7])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm]

theorem pubD_refl (s : State) : PubD s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-! ## The base state for the shared code -/

/-- The entry state `s` with memory `m` and `rc` in `r0`. -/
def bx (s : State) (m : Mem) (rc : Nat) : State :=
  { s with mem := m, gpr := fun r => if r = .r0 then BitVec.ofNat 64 rc else s.gpr r }

/-- The working space, of the base state. -/
abbrev SX : State → Addr := fun x => stackArg x 13

/-- `r15`–`r23`, of the base state. -/
def VX (x : State) : Reg → BitVec 64 := vD x (x.gpr .r0).toNat

/-- What the shared code needs of the base state. -/
def PreX (x : State) : Prop := Fits SX x

/-- The base state's public data: the stack pointer and the working space. -/
def PubX (a x : State) : Prop := x.sp = a.sp ∧ stackArg x 13 = stackArg a 13

theorem okX : OkS SX PreX PubX := ⟨id, fun p => p.1, fun p => p.2⟩

section
variable {s : State} (P : PreD s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) (rc : Nat)
include P hm

/-- The stack arguments, in the base state. -/
theorem stackArg_bx {i : Nat} (hi : i < 15) : stackArg (bx s m rc) i = stackArg s i := by
  show m.readW (stackArgAddr s i) 64 = s.mem.readW (stackArgAddr s i) 64
  exact hm.readW (in_aR hi) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact P.ka.symm
    · exact P.sa.symm) (by decide)

theorem stackArg_wm {i : Nat} (hi : i < 15) : stackArg (withMem s m) i = stackArg s i :=
  stackArg_bx P hm 0 hi

/-- `Base` for the shared code, from the decoding's. -/
theorem toX (hrc : rc ≤ 2) {t : State} (b : Base (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ Base SX VX (bx s m rc) t := by
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have g : ∀ r, r ≠ .r0 → (bx s m rc).gpr r = s.gpr r := fun r hr => by simp [bx, hr]
  have f := fits P (s' := bx s m rc) rfl rfl
  have eSC : SC SX (bx s m rc) = SC (SD s) (withMem s m) := by simp only [SC, h13]
  refine ⟨⟨f.sp1, by rw [h13]; exact f.sc, by rw [eSC]; exact f.ksc, by rw [h13]; exact f.wS⟩,
    ⟨⟨b.sv.sp, b.sv.wr, fun r hr => by rw [g r (by revert r; decide)]; exact b.sv.hi r hr,
      fun p hp => (b.sv.sv p hp).trans (g p.1 (by revert p; decide)).symm, b.sv.ls⟩, b.rd, b.r14.trans h13.symm,
      fun r hr => ?_, by rw [eSC]; exact b.mem⟩⟩
  have e0 : ((bx s m rc).gpr .r0).toNat = rc := by
    show (BitVec.ofNat 64 rc).toNat = rc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [b.vs r hr]
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VX, vD, e0, g _ (show Reg.r7 ≠ .r0 by decide), g _ (show Reg.r3 ≠ .r0 by decide),
      g _ (show Reg.r5 ≠ .r0 by decide), g _ (show Reg.r21 ≠ .r0 by decide), g _ (show Reg.r22 ≠ .r0 by decide),
      g _ (show Reg.r23 ≠ .r0 by decide), stackArg_bx P hm rc (i := 9) (by decide),
      stackArg_bx P hm rc (i := 10) (by decide)]

end

/-! ## After the private operation -/

/-- `t` has the decoding's `Base` from an entry state with `a`'s public data. -/
def DX (a t : State) : Prop :=
  ∃ s m, PreD s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t

theorem DX.of_after {a s v : State} (P : PreD s) (p : PubD a s) (A : AfterPriv s v) : DX a v :=
  ⟨s, v.mem, P, p, A.mem, A.base⟩

theorem DX.only {a t t' : State} {rs : List Reg} (h : DX a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : DX a t' :=
  let ⟨s, m, P, p, hm, b⟩ := h; ⟨s, m, P, p, hm, b.only (fitsM P) o hrs⟩

/-- What `DX` fixes, from the anchor. -/
theorem DX.pins {a t : State} (h : DX a t) :
    t.sp = fb a ∧ t.gpr .r14 = stackArg a 13 ∧ t.gpr .r15 = a.gpr .r7 ∧ t.gpr .r16 = a.gpr .r3 ∧
      t.gpr .r17 = a.gpr .r5 ∧ t.gpr .r18 = stackArg a 9 ∧ t.gpr .r19 = stackArg a 10 := by
  obtain ⟨s, m, P, p, hm, b⟩ := h
  exact ⟨by rw [b.sp]; show fb s = fb a; rw [fb, fb, p.sp], b.r14.trans (p.args 13 (by decide)),
    by rw [Base.r15 b, p.g _ (by decide)], by rw [Base.r16 b, p.g _ (by decide)], by rw [Base.r17 b, p.g _ (by decide)],
    by rw [Base.r18 b, p.args 9 (by decide)], by rw [Base.r19 b, p.args 10 (by decide)]⟩

/-- The registers `DX` fixes are the same in both runs. -/
theorem dx_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → DX (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  fun x t₁ t₂ h₁ h₂ => by
    obtain ⟨s₁, a₁, b₁, c₁, d₁, e₁, f₁⟩ := (h x t₁ h₁).pins
    obtain ⟨s₂, a₂, b₂, c₂, d₂, e₂, f₂⟩ := (h x t₂ h₂).pins
    refine ⟨s₁.trans s₂.symm, fun r hr => ?_⟩
    have := hrs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
      f₁.trans f₂.symm]

/-- The base state of a run for the shared code. -/
theorem DX.toB {a t : State} (h : DX a t) : B SX VX PreX PubX a t := by
  obtain ⟨s, m, P, p, hm, b⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  exact ⟨_, pX, ⟨p.sp, (stackArg_bx P hm _ (by decide)).trans (p.args 13 (by decide))⟩, bX⟩

end VG.Proof.RsaOaep.PPC64LE.Dec
