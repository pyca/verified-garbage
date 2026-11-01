module

public import VerifiedGarbage.Proof.MlKem.X86_64.SampleNtt
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.SampleNtt
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`, constant time but for the seed

Two runs whose seeds (the declared leak) and pointers agree leak the same: the
prologue and the arguments of the calls are proven by the taint analysis, the
calls by the sponge functions' own proofs (`RelCT.callEx`), and the loop,
whose branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes the
same way and each store goes to the same address.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

variable (w16 : Bool)

/-- What holds of every run of `c` from `s` that `Q a` does, for any `a`
with `Pre a` (by determinism). -/
theorem WP.all {c : Prog isa} {s : State} {α : Sort _} {Pre : α → Prop} {Q : α → State → Prop}
    (h : ∀ a, Pre a → WP isa c s (Q a)) (hne : ∃ a, Pre a) : WP isa c s fun s' => ∀ a, Pre a → Q a s' := by
  obtain ⟨a₀, h₀⟩ := hne
  obtain ⟨t, s', e, -⟩ := h a₀ h₀
  refine ⟨t, s', e, fun a ha => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-! ## A try -/

theorem traceTry (r : Reg) {h : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block (snTry r w16)) h).isSome = true) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
      (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) (.block (snTry r w16)) fun _ _ => True :=
  taintRel [.rbp, .rdi] (fun x y h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2.1]) c

/-- The taint analysis of the two tries, of either width. -/
theorem try_taint : ∃ h₈ h₉ : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block (snTry .r8 w16)) h₈).isSome = true ∧
      (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block (snTry .r9 w16)) h₉).isSome = true := by
  cases w16
  · exact ⟨_, _, by taint_decide, by taint_decide⟩
  · exact ⟨_, _, by taint_decide, by taint_decide⟩

/-- The hypotheses of `snTry_ok`. -/
structure TryPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length < 256
  wr : WrA w16 s.wr aP
  st : Stored w16 s.mem aP L

/-- The coefficients after a try of the value in `r`. -/
def tryL (L : List Zq) (d : Nat) : List Zq := if d < q then L ++ [ofNat d] else L

theorem tryL_len (L : List Zq) (d : Nat) : (tryL L d).length ≤ L.length + 1 := by
  unfold tryL; split <;> simp

theorem snTry_all (r : Reg) (s : State) (hne : ∃ aP L, TryPre w16 s aP L) :
    WP isa (.block (snTry r w16)) s fun s' => ∀ aP L, TryPre w16 s aP L →
      s'.gpr .rdi = BitVec.ofNat 64 (tryL L ((s.gpr r).setWidth 32).toNat).length ∧
      Stored w16 s'.mem aP (tryL L ((s.gpr r).setWidth 32).toNat) ∧ Frame [cRegion w16 aP] s.mem s'.mem ∧
        Keep [.rdi, r] s s' := by
  have := WP.all (Pre := fun p : Addr × List Zq => TryPre w16 s p.1 p.2)
    (Q := fun p s' => s'.gpr .rdi = BitVec.ofNat 64 (tryL p.2 ((s.gpr r).setWidth 32).toNat).length ∧
      Stored w16 s'.mem p.1 (tryL p.2 ((s.gpr r).setWidth 32).toNat) ∧ Frame [cRegion w16 p.1] s.mem s'.mem ∧
        Keep [.rdi, r] s s')
    (fun p h => snTry_ok w16 r s h.rbp h.rdi h.len h.wr h.st) (by obtain ⟨aP, L, h⟩ := hne; exact ⟨(aP, L), h⟩)
  exact WP.mono this fun s' h aP L hp => h (aP, L) hp

/-! ## The middle of an iteration -/

/-- The hypotheses of `snMid_ok`. -/
structure MPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : WrA w16 s.wr aP
  st : Stored w16 s.mem aP L
  cf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))

/-- After the loads. -/
def R1 (s₁ s₂ : State) : Prop :=
  ∃ aP L, MPre w16 s₁ aP L ∧ MPre w16 s₂ aP L ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rcx = s₂.gpr .rcx

/-- After the first try. -/
structure P3 (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : WrA w16 s.wr aP
  st : Stored w16 s.mem aP L

def R3 (s₁ s₂ : State) : Prop :=
  ∃ aP L, P3 w16 s₁ aP L ∧ P3 w16 s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- After the comparison of `j` with 256. -/
def R4 (s₁ s₂ : State) : Prop :=
  ∃ aP L, P3 w16 s₁ aP L ∧ P3 w16 s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.cf = some (decide (L.length < 256)) ∧ s₂.cf = some (decide (L.length < 256))

theorem ofNat64_toNat' {j : Nat} (h : j ≤ 256) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem tailTry_ct : RelCT isa (R4 w16) (.ite .b (.block (snTry .r8 w16)) (.block [])) fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx := by
  obtain ⟨_, _, c8, _⟩ := try_taint w16
  refine RelCT.ite (fun x y ⟨aP, L, _, _, _, _, c1, c2⟩ => by show x.cf = y.cf; rw [c1, c2]) ?_ ?_
  · refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, TryPre w16 x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (tryL L ((x.gpr .r8).setWidth 32).toNat).length ∧
        Stored w16 x'.mem aP (tryL L ((x.gpr .r8).setWidth 32).toNat) ∧ Frame [cRegion w16 aP] x.mem x'.mem ∧
          Keep [.rdi, .r8] x x')
      (RelCT.mono (traceTry w16 .r8 c8) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e8, _, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e8]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _, _, c1, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [c1] at this; simpa using this
      exact ⟨snTry_all w16 .r8 x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        snTry_all w16 .r8 y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, _, ecx, c1, _⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [c1] at this; simpa using this
      rw [(f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩).2.2.2.gpr (by decide),
        (f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩).2.2.2.gpr (by decide), ecx]
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil)
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, ecx, _, _⟩, _⟩ f1 f2
    rw [f1, f2]; exact ecx

theorem cmp256_ct : RelCT isa (R3 w16) (.block [.alu .cmp .rdi (.imm 256)]) (R4 w16) :=
  RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧
      x'.gpr = x.gpr ∧ x'.rd = x.rd ∧ x'.wr = x.wr)
    (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    (fun x y _ => ⟨cmpRdi_ok x, cmpRdi_ok y⟩) fun x y x' y' ⟨aP, L, p1, p2, e8, ecx⟩ f1 f2 => by
      have ep : ∀ {s s' : State}, P3 w16 s aP L → (s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧
          s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr) → P3 w16 s' aP L ∧ s'.cf = some (decide (L.length < 256)) :=
        fun {s s'} p ⟨c, m, g, _, w⟩ => ⟨⟨by rw [g, p.rbp], by rw [g, p.rdi], p.len, by rw [w]; exact p.wr,
          by rw [m]; exact p.st⟩, by rw [c, p.rdi, ofNat64_toNat' p.len]⟩
      obtain ⟨q1, c1⟩ := ep p1 f1
      obtain ⟨q2, c2⟩ := ep p2 f2
      exact ⟨aP, L, q1, q2, by rw [f1.2.2.1, f2.2.2.1, e8], by rw [f1.2.2.1, f2.2.2.1, ecx], c1, c2⟩

theorem mid_ct : RelCT isa (R1 w16)
    (.ite .b (.seq (.block (snTry .r9 w16)) (.seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (.block (snTry .r8 w16)) (.block []))))
      (.block [])) fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx := by
  obtain ⟨_, _, _, c9⟩ := try_taint w16
  refine RelCT.ite (fun x y ⟨aP, L, p1, p2, _⟩ => by
      show x.cf = y.cf; rw [p1.cf, p2.cf, p1.rdi, p2.rdi]) ?_ ?_
  · refine RelCT.seq (R := R3 w16) ?_ (RelCT.seq (cmp256_ct w16) (tailTry_ct w16))
    refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, TryPre w16 x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (tryL L ((x.gpr .r9).setWidth 32).toNat).length ∧
        Stored w16 x'.mem aP (tryL L ((x.gpr .r9).setWidth 32).toNat) ∧ Frame [cRegion w16 aP] x.mem x'.mem ∧
          Keep [.rdi, .r9] x x')
      (RelCT.mono (traceTry w16 .r9 c9) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e9, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e9]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, ofNat64_toNat' p1.len] at this; simpa using this
      exact ⟨snTry_all w16 .r9 x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        snTry_all w16 .r9 y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, e9, e8, ecx⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, ofNat64_toNat' p1.len] at this; simpa using this
      obtain ⟨d1, s1, _, k1⟩ := f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩
      obtain ⟨d2, s2, _, k2⟩ := f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩
      rw [e9] at d1 s1
      have hl' := tryL_len L ((y.gpr .r9).setWidth 32).toNat
      exact ⟨aP, _, ⟨by rw [k1.gpr (by decide), p1.rbp], d1, by omega, by rw [k1.2.2]; exact p1.wr, s1⟩,
        ⟨by rw [k2.gpr (by decide), p2.rbp], d2, by omega, by rw [k2.2.2]; exact p2.wr, s2⟩,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e8], by rw [k1.gpr (by decide), k2.gpr (by decide), ecx]⟩
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil)
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, _, ecx⟩, _⟩ f1 f2
    rw [f1, f2]; exact ecx


/-! ## An iteration -/

/-- The hypotheses of `snBody_ok`. -/
structure BPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : WrA w16 s.wr aP
  st : Stored w16 s.mem aP L
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1
  r2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1

/-- Two runs at the start of an iteration, with the same coefficients sampled
and the same bytes to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  ∃ aP L, BPre w16 s₁ aP L ∧ BPre w16 s₂ aP L ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    ∀ k < 3, s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .rsi + BitVec.ofNat 64 k)

theorem load_ct : RelCT isa (BRel w16) (.block snLoad) (R1 w16) := by
  refine RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .r9 = BitVec.setWidth 64 (d1w (x.mem (x.gpr .rsi)) (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))) ∧
        x'.gpr .r8 = BitVec.setWidth 64 (d2w (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))
          (x.mem (x.gpr .rsi + BitVec.ofNat 64 2))) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .r9, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨_, _, _, _, esi, _⟩ r hr => by simp at hr; subst hr; exact esi) (by taint_decide))
    (fun x y ⟨_, _, p1, p2, _⟩ => ⟨snLoad_ok x p1.r0 p1.r1 p1.r2, snLoad_ok y p2.r0 p2.r1 p2.r2⟩) ?_
  intro x y x' y' ⟨aP, L, p1, p2, esi, ecx, eb⟩ ⟨⟨h9, h8, hc, hm, hdi⟩, k⟩ ⟨⟨h9', h8', hc', hm', hdi'⟩, k'⟩
  have e0 := eb 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at e0
  have mp : ∀ {s s' : State}, BPre w16 s aP L → s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) →
      s'.mem = s.mem → s'.gpr .rdi = s.gpr .rdi → Keep [.rax, .rdx, .r8, .r9, .rdi] s s' → MPre w16 s' aP L :=
    fun {s s'} p c m d kk => ⟨by rw [kk.gpr (by decide), p.rbp], by rw [d, p.rdi], p.len, by rw [kk.2.2]; exact p.wr,
      by rw [m]; exact p.st, by rw [c, d]⟩
  exact ⟨aP, L, mp p1 hc hm hdi k, mp p2 hc' hm' hdi' k', by rw [h9, h9', e0, eb 1 (by decide)],
    by rw [h8, h8', eb 1 (by decide), eb 2 (by decide)], by rw [k.gpr (by decide), k'.gpr (by decide), ecx]⟩

theorem step_ct : RelCT isa (fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx)
    (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    (fun x y _ => ⟨WP.mono (snStep_ok x) fun _ h => h.1.2.2.1, WP.mono (snStep_ok y) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, e]

theorem body_ct : RelCT isa (BRel w16) (snBody w16) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq (load_ct w16) (RelCT.seq (mid_ct w16) step_ct)


/-! ## The whole function -/

namespace SampleNtt

variable {w16}

section
variable {σ₁ σ₂ : State} (hq : (sampleKW w16).pub σ₁ σ₂)
include hq

theorem pub_B : B σ₁ = B σ₂ := hq.2.2.2.2
theorem pub_scr : scr σ₁ = scr σ₂ := hq.2.2.1
theorem pub_at (k : Nat) : at' σ₁ k = at' σ₂ k := by simp only [at', pub_scr hq]
theorem pub_aP : aP σ₁ = aP σ₂ := hq.2.1
theorem pub_sd : sd σ₁ = sd σ₂ := hq.1
theorem pub_Lt (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, pub_B hq]

end

/-- Two runs at iteration `t` of `N`, `n = N - t` iterations from the end. -/
def LI (w16 : Bool) (N n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, (sampleKW w16).pre σ₁ ∧ (sampleKW w16).pre σ₂ ∧ (sampleKW w16).pub σ₁ σ₂ ∧ n = N - t ∧ t < N ∧
    LAt w16 σ₁ N t s₁ ∧ LAt w16 σ₂ N t s₂

theorem bpre {σ : State} (hp : (sampleKW w16).pre σ) {N t : Nat} (hN : N ≤ 280) (ht : t < N) {s : State}
    (h : LAt w16 σ N t s) : BPre w16 s (aP σ) (Lt σ t) :=
  ⟨h.env.rbp, h.rdi, sampleAfter_length_le (a := []) (by simp) _ t, WrA.of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by simpa using lat_regions hp hN h (k := 0) (by omega), lat_regions hp hN h (by omega),
    lat_regions hp hN h (by omega)⟩

theorem li_brel {N n : Nat} (hN : N ≤ 280) {s₁ s₂ : State} (h : LI w16 N n s₁ s₂) : BRel w16 s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  refine ⟨aP σ₁, Lt σ₁ t, bpre p₁ hN ht l₁, by rw [pub_aP hq, pub_Lt hq]; exact bpre p₂ hN ht l₂,
    by rw [l₁.rsi, l₂.rsi, pub_at hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [out_byte l₁ (by omega), out_byte l₂ (by omega), pub_B hq]

theorem loop_ct {N : Nat} (hN : N ≤ 280) (n : Nat) :
    RelCT isa (LI w16 N n) (.loop (snBody w16) .ne) (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => LAt w16 σ N N s) := by
  refine RelCT.loop (M := isa) (LI w16 N) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, (sampleKW w16).pre p.1 ∧ p.2 < N ∧ LAt w16 p.1 N p.2 x →
      LAt w16 p.1 N (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (N - p.2) - 1 == 0))
    (RelCT.mono (body_ct w16) (fun x y h => li_brel hN h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all (fun p hp' => lat_step hp'.1 hN hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all (fun p hp' => lat_step hp'.1 hN hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    rw [zf_last hN ht] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = N := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ N := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨N - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂'⟩

theorem regs_pub {σ₁ σ₂ s₁ s₂ : State} (hq : (sampleKW w16).pub σ₁ σ₂) (e₁ : Env w16 σ₁ s₁) (e₂ : Env w16 σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  rw [e₁.rbx, e₂.rbx, e₁.rsp, e₂.rsp, pub_scr hq]; exact ⟨rfl, hq.2.2.2.1⟩

/-- `N` iterations of the loop, given the taint analysis of setting the counter. -/
theorem snLoop_ct {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (hN0 : 0 < N) (hN : N ≤ 280)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (cB : (taint.check (X86_64.Taint.ofRegs []) (.block [.mov32 .rcx (.imm n)]) hc).isSome = true) :
    RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub (fun σ s => I6 w16 σ (3 * N) s)) (snLoop n w16)
      (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => LAt w16 σ N N s) :=
  RelCT.seq (relInv (I' := fun σ s => IA w16 σ N s) (fun σ s _ h => latA h)
      (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => LAt w16 σ N 0 s) (fun σ s _ h => latB hn h)
        (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) cB))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, hN0, l₁, l₂⟩)
      (loop_ct hN N))

theorem nil_regs {P : State → State → Prop} : ∀ x y, P x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

theorem absorb_ct' : RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub (I1 w16))
    (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) (Rel2 (sampleKW w16).pre (sampleKW w16).pub (I2 w16)) :=
  relInv (fun σ s hp h => callB_ok hp h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, absorb_pre h₁.args, absorb_pre h₂.args, ?_, (covA p₁ h₁.env).1, (covA p₁ h₁.env).2,
        (covA p₂ h₂.env).1, (covA p₂ h₂.env).2, (regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
        ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
        h₁.args.r9, h₂.args.r9, pub_scr hq, pub_at hq, pub_sd hq, (regs_pub hq h₁.env h₂.env).2, and_self])

theorem pad_ct' : RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub (I3 w16))
    (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) (Rel2 (sampleKW w16).pre (sampleKW w16).pub (I4 w16)) :=
  relInv (fun σ s hp h => callD_ok hp h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct
    Proof.Sha3.X86_64.Stream.Pad.pad_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, pad_pre h₁.args, pad_pre h₂.args, ?_, (covP p₁ h₁.env).1, (covP p₁ h₁.env).2,
        (covP p₂ h₂.env).1, (covP p₂ h₂.env).2, (regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.r8 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.r8, h₂.args.r8, pub_scr hq, pub_at hq,
        (regs_pub hq h₁.env h₂.env).2, and_self])

theorem squeeze_ct' {len : Nat} (hl : len ≤ 840) : RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => I5 w16 σ len s)
    (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => I6 w16 σ len s) :=
  relInv (fun σ s hp h => callF_ok hp hl h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, squeeze_pre h₁.args, squeeze_pre h₂.args, ?_, (covS p₁ h₁.env hl).1,
        (covS p₁ h₁.env hl).2, (covS p₂ h₂.env hl).1, (covS p₂ h₂.env hl).2, (regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
        ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
        h₁.args.r9, h₂.args.r9, pub_scr hq, pub_at hq, (regs_pub hq h₁.env h₂.env).2, and_self])

/-- `snSample n`, given the taint analysis of the blocks with `n`. -/
theorem sample_ct' {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (h3 : (3 * n).toNat = 3 * N) (hN0 : 0 < N)
    (hN : N ≤ 280) {hE hB : VG.Taint.Hint X86_64.Taint.T}
    (cE : (taint.check (X86_64.Taint.ofRegs []) (.block (snSqzArgs (3 * n))) hE).isSome = true)
    (cB : (taint.check (X86_64.Taint.ofRegs []) (.block [.mov32 .rcx (.imm n)]) hB).isSome = true) :
    RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub (I1 w16)) (snSample n w16) (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => LAt w16 σ N N s) :=
  RelCT.seq absorb_ct' (RelCT.seq (relInv (I' := I3 w16) (fun σ s hp h => blkC_ok hp h)
    (taintRel [] nil_regs (by taint_decide))) (RelCT.seq pad_ct' (RelCT.seq
      (relInv (I' := fun σ s => I5 w16 σ (3 * N) s) (fun σ s hp h => blkE_ok hp h3 (by omega) h) (taintRel [] nil_regs cE))
      (RelCT.seq (squeeze_ct' (by omega)) (snLoop_ct hn hN0 hN cB)))))

/-- The check of `j`, and the 280 iterations if it is less than 256: both
runs go the same way, since they sampled the same coefficients. -/
theorem more_ct : RelCT isa (Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => LAt w16 σ 168 168 s) (snMore w16)
    (Rel2 (sampleKW w16).pre (sampleKW w16).pub (IEnd w16)) := by
  refine RelCT.seq (relInv (I' := IM w16) (fun σ s _ h => cmp_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.cf = y.cf; rw [h₁.cf, h₂.cf, pub_Lt hq]) ?_ ?_
  · refine RelCT.mono (P := Rel2 (sampleKW w16).pre (sampleKW w16).pub (IM w16)) (RelCT.seq (relInv (I' := I1 w16)
        (fun σ s hp h => redo_ok hp h.env) (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (regs_pub hq h₁.env h₂.env).1) (by taint_decide)))
      (sample_ct' (n := 280) (N := 280) (by decide) (by decide) (by omega) (by omega) (by taint_decide)
        (by taint_decide))) (fun _ _ h => h.1) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁.env, l₁.rdi, l₁.stored⟩, ⟨l₂.env, l₂.rdi, l₂.stored⟩⟩
  · refine RelCT.mono (P := Rel2 (sampleKW w16).pre (sampleKW w16).pub fun σ s => IM w16 σ s ∧ s.cf = some false)
      (relInv (I' := IEnd w16) (fun σ s _ h => WP.block_nil (skip_ok h.1 h.2)) (taintRel [] nil_regs (by taint_decide)))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hc⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hc⟩, ⟨h₂, ?_⟩⟩) fun _ _ h => h
    have hc' : x.cf = some false := hc
    rw [h₂.cf, ← pub_Lt hq, ← h₁.cf, hc']

end SampleNtt

open SampleNtt in
theorem sampleW_ct : ConstantTime isa (sampleKW w16).pre (sampleKW w16).pub (Impl.MlKem.X86_64.sampleNTTW w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := I1 w16) (fun σ s hp h => by subst h; exact proA_ok hp)
    (taintRel [.rdi, .rsi, .rdx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (sample_ct' (n := 168) (N := 168) (by decide) (by decide) (by omega) (by omega) (by taint_decide)
    (by taint_decide)) (RelCT.seq more_ct ?_)
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, l₁, l₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (regs_pub hq l₁.env l₂.env).1) (by taint_decide)

theorem sample_ct : ConstantTime isa sampleK.pre sampleK.pub Impl.MlKem.X86_64.sampleNTT := by
  rw [sampleK_eq]; exact sampleW_ct false

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sampleSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sample_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sampleNTT (Proof.MlKem.sampleNTTContract X86_64.abi 16) :=
  Verified.of_correct sample_correct sample_ct
    { pre := by sig_implies_pre [Proof.MlKem.sampleNTTContract, Proof.MlKem.sampleNTTSig, sampleK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlKem.sampleNTTContract, Proof.MlKem.sampleNTTSig, sampleK, X86_64.abi, X86_64.argRegs]
        dsimp only [sampleK] at h
        obtain ⟨hr, hp⟩ := h
        cases e : Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 34) with
        | none =>
          rw [e] at hr
          have h0 : BitVec.setWidth 32 (s'.gpr .rax) = 0 := hr
          exact ⟨fun h1 => absurd (h0.symm.trans h1) (by decide : (0 : BitVec 32) ≠ 1), .inr ⟨h0, e⟩⟩
        | some f =>
          rw [e] at hr
          have h1 : BitVec.setWidth 32 (s'.gpr .rax) = 1 := hr
          obtain ⟨hred, hf⟩ := hp f e
          exact ⟨fun _ => hred, .inl ⟨h1, Spec.MlKem.minIterations, by
            show Spec.MlKem.sampleNTT _ _ = _
            rw [e, hf]⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlKem.sampleNTTContract, Proof.MlKem.sampleNTTSig, sampleK, X86_64.abi,
          X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Proof.MlKem.sampleNTTContract, Proof.MlKem.sampleNTTSig, sampleK, X86_64.abi,
        X86_64.argRegs] [sampleSat] using sampleSat }

end VG.Proof.MlKem.X86_64
