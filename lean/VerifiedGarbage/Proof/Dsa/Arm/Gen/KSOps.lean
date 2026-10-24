module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KS
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: the operations on the arrays as pieces

Each operation of the key working space from one stage (`St`) to the next,
with what it writes recorded in the stage's arrays (`A`, `live`) or header
words (`KV`, `kls`). The taint analysis checks each with the key working
space's registers (`r7`–`r9`) public, which both runs agree on.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr sub3 sel copy bitOf orOne clrLow ptr)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A taint certificate with the key working space's registers public. -/
abbrev Cert7 (code : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9]) code hc).isSome = true

/-- Shorthand for the arrays' updates. -/
abbrev KU (A : Nat → Nat) (j v : Nat) : Nat → Nat := VG.Proof.Rsa.Arm.Keys.upd A j v

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem ks_vp {F Q : State → State → Prop} {cf : State → Cfg} {code : Prog isa} (cert : Cert7 code)
    (hF : ∀ σ s, F σ s → SS G σ (cf σ) s) (wp : ∀ σ s, F σ s → WP isa code s (Q σ)) : VP F code Q :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    have a := hF _ _ h₁; have b := hF _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a.r7, b.r7]
    · rw [a.r8, b.r8]
    · rw [a.r9, b.r9]) wp

/-- `[o] := [a] − [b]`, for `[b] ≤ [a]`. -/
theorem sub3_vp {o a b : Nat} (cert : Cert7 (sub3 o a b)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : c.A b ≤ c.A a) :
    VP (St G c X) (sub3 o a b) (St G { c with A := KU c.A o (c.A a - c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have ha' : a < nArrs := h.liveOk a ha
  have hb' : b < nArrs := h.liveOk b hb
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1) rfl
    ((sub3_ok hw ho ha' hb' (by decide) hoa hob).mono fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R f => ⟨h.of_op R f ho k ?_, x⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  have lt : num t.mem G.KB G.w o < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  have alt : c.A a < 2 ^ (32 * G.w) := va ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt alt
  rcases (by omega : (t.gpr .r11).toNat = 0 ∨ (t.gpr .r11).toNat = 1) with e | e <;> rw [e] at v
  · omega
  · have : M * 1 = M := Nat.mul_one M
    omega

/-- `[o] := [b]` if the header word `sl` is 1, else `[a]`. -/
theorem sel_vp {o a b sl : Nat} (cert : Cert7 (sel o a b sl)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ c.kls) (bit : c.KV sl ≤ 1) :
    VP (St G c X) (sel o a b sl)
      (St G { c with A := KU c.A o (if c.KV sl = 0 then c.A a else c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  have vs := h.ksl sl hsl
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o =
      (if slot s.mem G.KB sl = 0 then num s.mem G.KB G.w a else num s.mem G.KB G.w b)) rfl
    ((sel_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob (h.kslOk sl hsl).1 (by show slot s.mem G.KB sl ≤ 1; rw [vs]; exact bit)).mono
      fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f ho k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va, vb, vs]), x⟩

/-- `[o] := [a]`. -/
theorem copy_vp {o a : Nat} (cert : Cert7 (copy o a)) (ho : o < nArrs) (ha : a ∈ c.live) (hoa : o ≠ a) :
    VP (St G c X) (copy o a) (St G { c with A := KU c.A o (c.A a), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get ha
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o = num s.mem G.KB G.w a) rfl
    ((copy_ok hw ho (h.liveOk a ha) (by decide) hoa).mono fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f ho k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- The header word `sl` := `[j]`'s low bit. -/
theorem bitOf_vp {sl j : Nat} (cert : Cert7 (.block (bitOf sl j))) (hj : j ∈ c.live) (hsl : KlsOk sl) :
    VP (St G c X) (.block (bitOf sl j)) (St G { c with KV := KU c.KV sl (c.A j % 2), kls := sl :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := []) (ds := [sl]) (P := fun t => slot t.mem G.KB sl = num s.mem G.KB G.w j % 2) rfl
    (by rw [← List.append_nil (bitOf sl j)]
        exact bitOf_ok hw (h.liveOk j hj) (by decide) hsl.1 fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_opS R f hsl k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- `[j]`'s low bit set. -/
theorem orOne_vp {j : Nat} (cert : Cert7 (.block (orOne j))) (hj : j ∈ c.live) :
    VP (St G c X) (.block (orOne j)) (St G { c with A := KU c.A j (2 * (c.A j / 2) + 1), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2) + 1) rfl
    (by rw [← List.append_nil (orOne j)]
        exact orOne_ok hw (h.liveOk j hj) (by decide) fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- `[j]`'s low bit cleared. -/
theorem clrLow_vp {j : Nat} (cert : Cert7 (.block (clrLow j))) (hj : j ∈ c.live) :
    VP (St G c X) (.block (clrLow j)) (St G { c with A := KU c.A j (2 * (c.A j / 2)), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2)) rfl
    (by rw [← List.append_nil (clrLow j)]
        exact clrLow_ok hw (h.liveOk j hj) (by decide) fun t w k v r _ => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

end

end VG.Proof.Dsa.Arm.Gen
