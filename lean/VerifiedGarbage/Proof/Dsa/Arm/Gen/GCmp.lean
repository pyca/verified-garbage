module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSOps
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: comparisons in the key working space

`ltS_vp`: the header word `d` := whether `[a] < [b]`, by the borrow of
`[aTmp] := [a] − [b]`; `andCmp_vp`: the header word `d` := the and of two
others, and Z iff it is 0; `slotCmp_vp`: Z iff a header word is 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr sub3 andS)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `[o] := [a] − [b]` into an array no stage keeps: the borrow in `r11`. -/
theorem sub3b_vp {o a b : Nat} (cert : Cert7 (sub3 o a b)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hol : o ∉ c.live) :
    VP (St G c X) (sub3 o a b)
      (fun σ t => St G c X σ t ∧ (t.gpr .r11).toNat = b2n (decide (c.A a < c.A b))) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1) rfl
    ((sub3_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob).mono fun t ⟨w, k, v, br, r⟩ =>
      ⟨w, k, ⟨v, br⟩, r⟩) fun t k ⟨v, br⟩ R f => ⟨?_, ?_⟩
  · have e := h.of_ks (A := c.A) (live := c.live) (KV := c.KV) (kls := c.kls) R f
      (h.arrs.keep k hw (fun j hj => ⟨h.liveOk j hj, by
        simp only [List.mem_singleton]; rintro rfl; exact hol hj⟩) (by simp))
      h.liveOk (fun d hd => by rw [k.slot (h.kslOk d hd).1 (by simp)]; exact h.ksl d hd) h.kslOk
    exact ⟨e, x⟩
  · simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
    rw [va, vb] at v
    have lt : num t.mem G.KB G.w o < 2 ^ (32 * G.w) := val32_lt _ _ _ _
    have blt : c.A b < 2 ^ (32 * G.w) := vb ▸ val32_lt _ _ _ _
    exact (VG.Proof.Rsa.sub32_of lt blt v br).2

/-- The header word `d` := `r11`. -/
theorem strR11_vp {d v : Nat} (cert : Cert7 (.block [.str .r11 .r8 d])) (hd : KlsOk d) :
    VP (fun σ s => St G c X σ s ∧ (s.gpr .r11).toNat = v) (.block [.str .r11 .r8 d])
      (St G { c with KV := KU c.KV d v, kls := d :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, r11⟩ => ?_
  have hw := h.ws
  have d4 : d + 4 ≤ 2 ^ 64 := by have := hd.1; simp only [hdr] at this; omega
  refine h.ksOp (js := []) (ds := [d]) (ws := []) (P := fun t => slot t.mem G.KB d = v) rfl
    (wp_strSlot hw hd.1 fun t u => WP.block_nil ⟨hw.of_mupd u,
      Keep.of_slot (by rw [u.mem]; exact VG.Proof.Mont.writeW32_outside _ _ _ d4) (by simp),
      by rw [u.mem, slot_write_self]; exact r11, u.rest []⟩) fun t k e R f => ⟨h.of_opS R f hd k e, x⟩

/-- The header word `d` := whether `[a] < [b]`. -/
theorem ltS_vp {d a b : Nat} (c1 : Cert7 (sub3 aTmp a b)) (c2 : Cert7 (.block [.str .r11 .r8 d]))
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live) (hd : KlsOk d) :
    VP (St G c X) (VG.Impl.Rsa.Arm.Keys.seqs (ltS d a b))
      (St G { c with KV := KU c.KV d (b2n (decide (c.A a < c.A b))), kls := d :: c.kls } X) :=
  VP.seq (sub3b_vp c1 (by decide) ha hb hta htb htl) (strR11_vp c2 hd)

/-- The header word `d` := `[a]` and `[b]` (each 0 or 1); Z iff it is 0. -/
theorem andCmp_vp {d a b : Nat} (cert : Cert7 (.block (andS d a b ++ [.ldr .r1 .r8 d, .cmp .r1 (.imm 0)])))
    (hd : KlsOk d) (ha : a ∈ c.kls) (hb : b ∈ c.kls) (ba : c.KV a ≤ 1) (bb : c.KV b ≤ 1) :
    VP (St G c X) (.block (andS d a b ++ [.ldr .r1 .r8 d, .cmp .r1 (.imm 0)]))
      (fun σ t => St G { c with KV := KU c.KV d (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0), kls := d :: c.kls } X σ t ∧
        isa.eval .eq t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va : slot (G.ksState s).mem G.KB a = c.KV a := h.ksl a ha
  have vb : slot (G.ksState s).mem G.KB b = c.KV b := h.ksl b hb
  have d4 : d + 4 ≤ 2 ^ 64 := by have := hd.1; simp only [hdr] at this; omega
  refine h.ksOp (js := []) (ds := [d]) (ws := VG.Proof.Rsa.Arm.Keys.opRegs) (P := fun t =>
      slot t.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) ∧
      isa.eval .eq t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) rfl ?_
    fun t k ⟨e, z⟩ R f => ⟨⟨h.of_opS R f hd k e, x⟩, z⟩
  refine andS_ok hw hd.1 (h.kslOk a ha).1 (h.kslOk b hb).1 (by rw [va]; exact ba) (by rw [vb]; exact bb)
    fun t₁ w₁ k₁ v₁ R₁ => wp_ldrSlot w₁ hd.1 fun t₂ u₂ => wp_cmp (op2_imm (by decide)) fun t₃ f₃ z₃ =>
      WP.block_nil ⟨w₁.of ?_ ?_ ?_ ?_, k₁.trans (by rw [f₃.mem, u₂.mem]; exact Keep.refl _ _ _ _ _), ?_, ?_⟩
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.wr, u₂.wr]
  · have v : slot t₃.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
      rw [f₃.mem, u₂.mem, v₁, va, vb]
    refine ⟨v, ?_⟩
    rw [eval_eq, z₃, u₂.gpr]
    have r : (t₁.mem.readW (off (State.addr G.KB) d) 32).toNat = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
      have := v; rw [f₃.mem, u₂.mem] at this; exact this
    have e0 : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
    rw [e0]
    congr 1
    by_cases hc : c.KV a = 1 ∧ c.KV b = 1
    · have : t₁.mem.readW (off (State.addr G.KB) d) 32 = 1 := BitVec.eq_of_toNat_eq (by rw [r]; simp [hc])
      rw [this]; simp [hc]
    · have : t₁.mem.readW (off (State.addr G.KB) d) 32 = 0 := BitVec.eq_of_toNat_eq (by rw [r]; simp [hc])
      rw [this]; simp [hc]
  · exact R₁.trans ((u₂.rest (by decide)).trans (f₃.rest _))

/-- Z iff the header word `d` (0 or 1) is 0. -/
theorem slotCmp_vp {d : Nat} (cert : Cert7 (.block [.ldr .r1 .r8 d, .cmp .r1 (.imm 0)])) (hd : d ∈ c.kls)
    (bd : c.KV d ≤ 1) :
    VP (St G c X) (.block [.ldr .r1 .r8 d, .cmp .r1 (.imm 0)])
      (fun σ t => St G c X σ t ∧ isa.eval .eq t = some (decide (c.KV d = 0))) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have vd := h.ksl d hd
  refine h.ksOp (js := []) (ds := []) (ws := [.r1]) (P := fun t => t.mem = s.mem ∧
      isa.eval .eq t = some (decide (c.KV d = 0))) rfl ?_ fun t _ ⟨m, z⟩ R _ => ⟨⟨h.of_rest R m, x⟩, z⟩
  refine wp_ldrSlot hw (h.kslOk d hd).1 fun t₂ u₂ => wp_cmp (op2_imm (by decide)) fun t₃ f₃ z₃ =>
    WP.block_nil ⟨hw.of ?_ ?_ ?_ ?_, by rw [f₃.mem, u₂.mem]; exact Keep.refl _ _ _ _ _, ⟨by rw [f₃.mem, u₂.mem]; rfl, ?_⟩,
      (u₂.rest (ws := [.r1]) (by simp)).trans (f₃.rest _)⟩
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.gpr, u₂.other _ (by decide)]
  · rw [f₃.wr, u₂.wr]
  · have r : ((G.ksState s).mem.readW (off (State.addr G.KB) d) 32).toNat = c.KV d := vd
    have e0 : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
    rw [eval_eq, z₃, u₂.gpr, e0]
    congr 1
    rcases (by omega : c.KV d = 0 ∨ c.KV d = 1) with e | e
    · have : (G.ksState s).mem.readW (off (State.addr G.KB) d) 32 = 0 := BitVec.eq_of_toNat_eq (by rw [r, e]; rfl)
      rw [this, e]; rfl
    · have : (G.ksState s).mem.readW (off (State.addr G.KB) d) 32 = 1 := BitVec.eq_of_toNat_eq (by rw [r, e]; rfl)
      rw [this, e]; rfl

end

end VG.Proof.Dsa.Arm.Gen
