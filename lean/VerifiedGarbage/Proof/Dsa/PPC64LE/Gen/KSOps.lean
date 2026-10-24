module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KS
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the operations on the key working space as pieces

A stage of the arithmetic (`KSt`) is a stage of the search with the key
working space's registers set (`KR`). Each operation of
`Proof/Rsa/PPC64LE/KeyOps.lean` and `KeyBits.lean` from it, as a piece
(`ks_vp`): the taint analysis takes `r28`–`r31` public.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs sub3_ok sel_ok copy_ok bitOf_ok orOne_ok clrLow_ok stBorrow_ok)
open VG.Impl.Rsa.PPC64LE.Keys (sub3 sel copy bitOf orOne clrLow stBorrow)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `A` with `j ↦ v`. -/
abbrev KU := VG.Proof.Rsa.KeyWorkspace.upd

/-- The memory frame of the key operations. -/
abbrev KKeep := VG.Proof.Rsa.KeyWorkspace.Keep

/-- A stage of the arithmetic. -/
abbrev KSt (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := St G c X σ s ∧ KR G s

/-- The taint analysis of code in the key working space. -/
abbrev CertK (code : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31]) code hc).isSome = true

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- An operation in the key working space, from a state of the search. -/
theorem SS.ksOp {STK : Nat} {σ s : State} (h : SS G STK σ c s) {code : Prog isa} (hn : code.noCalls = true)
    {js ds : List Nat} {P : State → Prop} {ws : List Reg}
    (hwp : WP isa code (G.ksState s) fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧
      KKeep G.KB G.w js ds s.mem t.mem ∧ P t ∧ VG.Proof.Bignum.PPC64LE.Keep ws (G.ksState s) t) {Q : State → Prop}
    (k : ∀ t, KKeep G.KB G.w js ds s.mem t.mem → P (G.ksState t) → Keep ws s t → t.sp = s.sp →
      Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q :=
  h.ksWP hn hwp fun t ⟨_, kp, p, r⟩ hr hw f => k t kp p ⟨r.gpr, hr, hw⟩ r.sp f

/-- A piece in the key working space. -/
theorem ks_vp {F Q : State → State → Prop} {cf : State → Cfg} {code : Prog isa} (cert : CertK code)
    (hF : ∀ σ s, F σ s → SS G 176 σ (cf σ) s ∧ KR G s) (wp : ∀ σ s, F σ s → WP isa code s (Q σ)) : VP F code Q :=
  VP.pub (G := G) (fun σ s hs => ⟨(hF σ s hs).1.gi.r28, by rw [(hF σ s hs).1.gi.sp, ← (hF σ s hs).1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      have a := (hF _ _ h₁).2; have b := (hF _ _ h₂).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]) wp

/-- `[o] := [a] − [b]`, for `[b] ≤ [a]`. -/
theorem sub3_vp {o a b : Nat} (cert : CertK (sub3 o a b)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : c.A b ≤ c.A a) :
    VP (KSt G c X) (sub3 o a b) (KSt G { c with A := KU c.A o (c.A a - c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r9).toNat ∧ (t.gpr .r9).toNat ≤ 1) rfl
    ((sub3_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob).mono fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨h.of_op R sp f ho k ?_, x⟩, kr.of_keep R⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  have lt : num t.mem G.KB G.w o < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  have alt : c.A a < 2 ^ (32 * G.w) := va ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt alt
  rcases (by omega : (t.gpr .r9).toNat = 0 ∨ (t.gpr .r9).toNat = 1) with e | e <;> rw [e] at v
  · omega
  · have : M * 1 = M := Nat.mul_one M
    omega

/-- `[o] := [b]` if the header word `sl` is 1, else `[a]`. -/
theorem sel_vp {o a b sl : Nat} (cert : CertK (sel o a b sl)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ c.kls) (bit : c.KV sl ≤ 1) :
    VP (KSt G c X) (sel o a b sl)
      (KSt G { c with A := KU c.A o (if c.KV sl = 0 then c.A a else c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  have vs := h.ksl sl hsl
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o =
      (if slot s.mem G.KB sl = 0 then num s.mem G.KB G.w a else num s.mem G.KB G.w b)) rfl
    ((sel_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob (h.kslOk sl hsl).1
      (by show slot s.mem G.KB sl ≤ 1; rw [vs]; exact bit)).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va, vb, vs]), x⟩, kr.of_keep R⟩

/-- `[o] := [a]`. -/
theorem copy_vp {o a : Nat} (cert : CertK (copy o a)) (ho : o < nArrs) (ha : a ∈ c.live) (hoa : o ≠ a) :
    VP (KSt G c X) (copy o a) (KSt G { c with A := KU c.A o (c.A a), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o = num s.mem G.KB G.w a) rfl
    ((copy_ok hw ho (h.liveOk a ha) (by decide) hoa).mono fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- The header word `sl` := `[j]`'s low bit. -/
theorem bitOf_vp {sl j : Nat} (cert : CertK (.block (bitOf sl j))) (hj : j ∈ c.live) (hsl : KlsOk sl) :
    VP (KSt G c X) (.block (bitOf sl j)) (KSt G { c with KV := KU c.KV sl (c.A j % 2), kls := sl :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := []) (ds := [sl]) (P := fun t => slot t.mem G.KB sl = num s.mem G.KB G.w j % 2) rfl
    (by rw [← List.append_nil (bitOf sl j)]
        exact bitOf_ok hw (h.liveOk j hj) (by decide) hsl.1 fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hsl k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit set. -/
theorem orOne_vp {j : Nat} (cert : CertK (.block (orOne j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (orOne j))
      (KSt G { c with A := KU c.A j (2 * (c.A j / 2) + 1), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := [])
    (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2) + 1) rfl
    (by rw [← List.append_nil (orOne j)]
        exact orOne_ok hw (h.liveOk j hj) (by decide) fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit cleared. -/
theorem clrLow_vp {j : Nat} (cert : CertK (.block (clrLow j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (clrLow j))
      (KSt G { c with A := KU c.A j (2 * (c.A j / 2)), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2)) rfl
    (by rw [← List.append_nil (clrLow j)]
        exact clrLow_ok hw (h.liveOk j hj) (by decide) fun t w k v r _ => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
