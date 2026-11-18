module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PArith
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Dsa.Arm.PowVerified
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Rsa.BoolNat
import VerifiedGarbage.Proof.Rsa.Sub32

/-! ### `Dsa.Arm.Gen.GStep`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.GCmp`, which only this module used -/

section

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
  have d4 : d + 4 ≤ 2 ^ 64 := by have := hd.1; simp only [hdr] at this; omega_using [this]
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
theorem andCmp_vp {d a b : Nat} (cert : Cert7 (.block (andS d a b ++ ([.ldr .r1 .r8 d, .cmp .r1 (.imm 0)] : List Instr))))
    (hd : KlsOk d) (ha : a ∈ c.kls) (hb : b ∈ c.kls) (ba : c.KV a ≤ 1) (bb : c.KV b ≤ 1) :
    VP (St G c X) (.block (andS d a b ++ ([.ldr .r1 .r8 d, .cmp .r1 (.imm 0)] : List Instr)))
      (fun σ t => St G { c with KV := KU c.KV d (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0), kls := d :: c.kls } X σ t ∧
        isa.eval .eq t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va : slot (G.ksState s).mem G.KB a = c.KV a := h.ksl a ha
  have vb : slot (G.ksState s).mem G.KB b = c.KV b := h.ksl b hb
  have d4 : d + 4 ≤ 2 ^ 64 := by have := hd.1; simp only [hdr] at this; omega_using [this]
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
    rcases (by omega_using [bd] : c.KV d = 0 ∨ c.KV d = 1) with e | e
    · have : (G.ksState s).mem.readW (off (State.addr G.KB) d) 32 = 0 := BitVec.eq_of_toNat_eq (by rw [r, e]; rfl)
      rw [this, e]; rfl
    · have : (G.ksState s).mem.readW (off (State.addr G.KB) d) 32 = 1 := BitVec.eq_of_toNat_eq (by rw [r, e]; rfl)
      rw [this, e]; rfl

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.GCopy`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: copies between the arrays and `scratch`

`copyOut_vp`: the low `n` bytes of array `j` to byte `dst` of `scratch`, as
they are (little-endian); `copyIn_vp`: array `j` := the number of
`4 w` bytes at byte `src` of `scratch`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Byte `dst` of `scratch` := the low `n` bytes of `[j]`, little-endian. -/
theorem copyOut_vp {L j dst n : Nat} (cert : Cert7 (copyN (scr L .r0 dst) (ptr .r1 j) n)) (hL : L = G.pLen)
    (hj : j ∈ c.live) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (hd : dst + n ≤ sK G.pLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart dst n x) {E : Mem → Prop}
    (hE : ∀ m m', E m → Frame [G.rs dst n] m m' → E m') :
    VP (fun σ s => St G c X σ s ∧ E s.mem) (copyN (scr L .r0 dst) (ptr .r1 j) n)
      (fun σ t => St G { c with cl := cl' } X σ t ∧ E t.mem ∧
        (t.mem.read (G.sa dst) n).toNat = c.A j % 2 ^ (8 * n)) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, ex⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  obtain hjN := h.liveOk j hj
  obtain fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  obtain w96 : G.w ≤ 96 := by simp only [GP.w]; omega_arith
  obtain inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  obtain ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega_arith)
  obtain e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  obtain as : State.addr (G.scr + BitVec.ofNat 32 dst) = G.sa dst := gi.saddr (by omega_arith)
  obtain va := h.arrs.get hj
  unfold copyN
  rw [List.append_assoc]
  refine WP.seq (h.ptr_ok (r := .r1) (by decide) (by simp only [nArrs] at hjN; omega_arith) fun s₁ p₁ R₁ m₁ => ?_)
  obtain r8₁ : s₁.gpr .r8 = G.KB := by rw [R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r0) (o := dst) r8₁ rfl l (by omega_arith) fun s₂ v₂ R₂ M₂ => ?_
  refine wp_movw fun s₃ u₃ => WP.block_nil ?_
  obtain R₃ : Rest [.r0, .r1, .r12, .lr] s s₃ := (R₁.mono (by simp)).trans ((R₂.mono (by simp)).trans
    (u₃.rest (by simp)))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, M₂, m₁]
  obtain srcFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]; omega_arith
  obtain dstFit : (G.scr + BitVec.ofNat 32 dst).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₃ (src := G.KB + BitVec.ofNat 32 (arr G.w j))
    (dst := G.scr + BitVec.ofNat 32 dst) (n := n) hn0 srcFit dstFit (by omega_arith)
    ⟨G.rScr, List.mem_append_right _ (by rw [R₃.wr]; exact inS), by
      rw [ad, e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨G.rScr, by rw [R₃.wr]; exact inS, by rw [as]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (by rw [u₃.other _ (by decide), v₂])
    (by rw [u₃.other _ (by decide), R₂.gpr _ (by decide), p₁])
    (by rw [u₃.gpr, setWidth_ofNat16 (by omega_arith)])) ?_
  rintro t ⟨rt, ft, _, Rt⟩
  rw [as, m₃] at ft
  rw [as, ad, m₃] at rt
  refine ⟨⟨h.of_scr ((R₃.mono (ws' := [.r0, .r1, .r2, .r12, .lr]) (by simp)).trans (Rt.mono (by simp))) (o := dst) (n := n) hd (ft.mono (by simp))
    fun y hy => .inl (hcl y hy), x⟩, hE _ _ ex ft, ?_⟩
  rw [rt, VG.Proof.Rsa.Arm.CrtValues.read_low _ _ (n := G.w) hnw]
  exact congrArg (· % 2 ^ (8 * n)) va

/-- `[j]` := the number of `4 w` bytes at byte `src` of `scratch`. -/
theorem copyIn_vp {L j src n v : Nat} (cert : Cert7 (copyN (ptr .r0 j) (scr L .r1 src) n)) (hL : L = G.pLen)
    (hjN : j < nArrs) (hn : n = 4 * G.w) (hs : src + n ≤ sK G.pLen) :
    VP (fun σ s => St G c X σ s ∧ (s.mem.read (G.sa src) n).toNat = v) (copyN (ptr .r0 j) (scr L .r1 src) n)
      (St G { c with A := KU c.A j v, live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, ev⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  obtain fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  obtain w96 : G.w ≤ 96 := by simp only [GP.w]; omega_arith
  obtain w1 : 1 ≤ G.w := by simp only [GP.w]; omega_arith
  obtain inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  obtain ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega_arith)
  obtain e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  obtain as : State.addr (G.scr + BitVec.ofNat 32 src) = G.sa src := gi.saddr (by omega_arith)
  unfold copyN
  rw [List.append_assoc]
  refine WP.seq (scr_ok (d := .r1) (o := src) h.r8 rfl l (by omega_arith) fun s₁ v₁ R₁ M₁ => ?_)
  obtain h₁ := h.of_rest (R₁.mono (ws' := [.r12, .r1]) (by simp)) M₁
  refine h₁.ptr_ok (r := .r0) (by decide) (by simp only [nArrs] at hjN; omega_arith) fun s₂ p₂ R₂ m₂ => ?_
  refine wp_movw fun s₃ u₃ => WP.block_nil ?_
  obtain R₃ : Rest [.r0, .r1, .r12, .lr] s s₃ := (R₁.mono (by simp)).trans ((R₂.mono (by simp)).trans
    (u₃.rest (by simp)))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, m₂, M₁]
  obtain srcFit : (G.scr + BitVec.ofNat 32 src).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]; omega_arith
  obtain dstFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₃ (src := G.scr + BitVec.ofNat 32 src)
    (dst := G.KB + BitVec.ofNat 32 (arr G.w j)) (n := n) (by omega_arith) srcFit dstFit (by omega_arith)
    ⟨G.rScr, List.mem_append_right _ (by rw [R₃.wr]; exact inS), by
      rw [as]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨G.rScr, by rw [R₃.wr]; exact inS, by rw [ad, e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
    (by rw [u₃.other _ (by decide), p₂])
    (by rw [u₃.other _ (by decide), R₂.gpr _ (by decide), v₁])
    (by rw [u₃.gpr, setWidth_ofNat16 (by omega_arith)])) ?_
  rintro t ⟨rt, ft, _, Rt⟩
  rw [ad, m₃] at ft rt
  rw [as] at rt
  obtain hrK : Region.Sub ⟨off (State.addr G.KB) (arr G.w j), n⟩ ⟨off (State.addr G.KB) (arr G.w j), S G.w⟩ :=
    fun a h => by simp only [Region.Contains] at h ⊢; omega_arith
  obtain k : Keep G.KB G.w [j] [] s.mem t.mem :=
    VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr (ft.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hrK⟩) (by omega_arith)
  obtain fK : Frame [G.rK] s.mem t.mem := ft.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rK, List.mem_singleton_self _, Offset.sub_base (State.addr G.KB) (by omega_arith)⟩
  obtain vw : num t.mem G.KB G.w j = v := by
    rw [← ev, ← rt, hn]
    exact (VG.Proof.Bignum.read_eq_val32 t.mem (State.addr G.KB) G.w (arr G.w j)).symm
  exact ⟨h.of_op ((R₃.mono (ws' := [.r0, .r1, .r2, .r12, .lr]) (by simp)).trans (Rt.mono (by simp))) fK hjN k vw, x⟩

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.GPow`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: the exponentiation

`powCall_vp`: `vg_dsa_pow_{n}_{e}` (`Impl/Dsa/Arm/Pow.lean`) called on the
working space at `sA`, under its contract on ARM (`Proof.Dsa.Arm.Pow.powArm`):
the number at its result is the base to the exponent modulo the modulus.
`PowOk n e code`: a verified exponentiation that uses no more stack than
the frame leaves below it.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Arm.FrameStack (armStack belowA)

/-- A verified exponentiation. -/
structure PowOk (n e : Nat) (code : Prog isa) : Prop where
  correct : ∀ s, (Proof.Dsa.Arm.Pow.powArm n e).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Dsa.Arm.Pow.powArm n e).post s s'
  ct : ConstantTime isa (Proof.Dsa.Arm.Pow.powArm n e).pre (Proof.Dsa.Arm.Pow.powArm n e).pub code
  stack : armStack code ≤ 176

/-- The exponentiation's numbers in its working space at `sA`. -/
abbrev PowIn (G : GP) (n e pv hv ev : Nat) (m : Mem) : Prop :=
  (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv ∧ (m.read (G.sa (sA + baseS n)) (8 * n)).toNat = hv ∧
    (m.read (G.sa (sA + expS n)) (4 * e)).toNat = ev

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The working space's region. -/
abbrev GP.rPow (G : GP) : Region := ⟨G.sa sA, wa G.pLen / 8 * 8⟩

theorem powCall_vp {L n e : Nat} {name : String} {code : Prog isa} (ok : PowOk n e code) (hL : L = G.pLen)
    (hctx : contextBytes n ≤ wa G.pLen) {pv hv ev : Nat} (hodd : pv % 2 = 1) (hgt : 1 < pv) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa G.pLen) x) :
    VP (fun σ s => St G c X σ s ∧ PowIn G n e pv hv ev s.mem)
      (.seq (.block (scr L .r0 sA ++ ([.movw .r1 (BitVec.ofNat 16 (wa L / 8))] : List Instr))) (.call name code))
      (fun σ t => St G { c with cl := cl' } X σ t ∧
        (t.mem.read (G.sa (sA + resS n)) (8 * n)).toNat = hv ^ ev % pv) := by
  subst hL
  have w8 : wa G.pLen / 8 * 8 = wa G.pLen := by simp only [wa]; omega_arith
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ PowIn G n e pv hv ev s.mem) ∧
      s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa G.pLen / 8))
    (VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 2)])), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.r8, h₂.1.1.r8])
      fun σ s ⟨⟨h, x⟩, pin⟩ => ?_) ?_
  · have big := h.gi.scrBig
    have l := h.lens
    refine scr_ok (d := .r0) (o := sA) h.r8 rfl l (by simp only [sK]; omega_arith) fun s₁ v₁ R₁ M₁ =>
      wp_movw fun s₂ u₂ => WP.block_nil ⟨⟨⟨h.of_rest ((R₁.mono (by simp)).trans (u₂.rest (by simp)) :
        Rest [.r12, .r0, .r1] s s₂) (by rw [u₂.mem, M₁]), x⟩, by rw [u₂.mem, M₁]; exact pin⟩,
        by rw [u₂.other _ (by decide), v₁], ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : wa G.pLen / 8 < 2 ^ 16 := by simp only [wa]; omega_arith
    omega_arith
  -- The call, from the working space and its length.
  have facts : ∀ σ s, (St G c X σ s ∧ PowIn G n e pv hv ev s.mem) ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧
      s.gpr .r1 = BitVec.ofNat 32 (wa G.pLen / 8) →
      (Proof.Dsa.Arm.Pow.powArm n e).pre (s.callEntry.withRegions [] [G.rPow]) ∧
      Covers ([] ++ [G.rPow]) (s.rd ++ s.wr) ∧ Covers [G.rPow] s.wr ∧ armStack code ≤ s.sp.toNat ∧
      State.addr (s.gpr .r0) = G.sa sA ∧ ((s.gpr .r1).toNat = wa G.pLen / 8) := fun σ s ⟨⟨⟨h, _⟩, pin⟩, r0, r1⟩ => by
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
    have l := h.lens
    have aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega_arith) (by simp only [wa]; omega_arith)
    have r1n : (s.gpr .r1).toNat = wa G.pLen / 8 := by
      rw [r1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [wa]; omega_arith)
    have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
    have cov : Covers [G.rPow] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨G.rScr, List.mem_singleton_self _, sA, rfl, show sA + wa G.pLen / 8 * 8 ≤ G.scrLen * 8 by
        simp only [sK] at big; omega_arith⟩).trans
      (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
    have e0 : ∀ o, State.addr (s.gpr .r0) + BitVec.ofNat 64 o = G.sa (sA + o) := fun o => by
      rw [r0, aS]; simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, Covers.right cov, cov, ?_, by rw [r0, aS], r1n⟩
    · show [G.rPow] = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩]
      rw [r0, aS, r1n]
    · show (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
      rw [r1n, r0, h.toNat (by simp only [sK]; omega_arith)]; simp only [sK] at big; omega_arith
    · show contextBytes n ≤ 8 * (s.gpr .r1).toNat
      rw [r1n]; omega_arith
    · show Proof.Dsa.ModPow.numAt s.mem (State.addr (s.gpr .r0)) (modS n) (8 * n) % 2 = 1
      rw [Proof.Dsa.ModPow.numAt, e0, pin.1]; exact hodd
    · show 1 < Proof.Dsa.ModPow.numAt s.mem (State.addr (s.gpr .r0)) (modS n) (8 * n)
      rw [Proof.Dsa.ModPow.numAt, e0, pin.1]; exact hgt
    · rw [gi.sp]; have := gi.sp176; have := ok.stack; omega_arith
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call ok.correct ok.ct [] [G.rPow] fun s₁ s₂ ⟨h₁, h₂⟩ => ?_)
    fun σ s hs => ?_
  · obtain ⟨p₁, c₁, w₁, -, a₁, -⟩ := facts _ _ h₁
    obtain ⟨p₂, c₂, w₂, -, a₂, -⟩ := facts _ _ h₂
    refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · show s₁.sp = s₂.sp
      rw [h₁.1.1.1.gi.sp, h₂.1.1.1.gi.sp]
    · show s₁.callEntry.gpr .r0 = s₂.callEntry.gpr .r0
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.2.1, h₂.2.1]
    · show s₁.callEntry.gpr .r1 = s₂.callEntry.gpr .r1
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.2.2, h₂.2.2]
    · -- The modulus is the same number in both runs.
      have mv : ∀ {s : State}, State.addr (s.gpr .r0) = G.sa sA → PowIn G n e pv hv ev s.mem →
          Proof.Dsa.ModPow.numAt (s.callEntry.withRegions [] [G.rPow]).mem
            (State.addr ((s.callEntry.withRegions [] [G.rPow]).gpr .r0)) (modS n) (8 * n) = pv := fun {s} a pin => by
        simp only [Proof.Dsa.ModPow.numAt, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
          State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide)]
        rw [a, ← pin.1]; simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (mv a₁ h₁.1.2).trans (mv a₂ h₂.1.2).symm
  obtain ⟨pre, hc, hw, hd, a0, r1n⟩ := facts σ s hs
  obtain ⟨⟨⟨h, x⟩, pin⟩, r0, r1⟩ := hs
  refine FrameStack.WP.callF ok.correct pre hc hw hd fun s' hrd hwr hsp f hpres hpost => ?_
  have gi := h.gi
  have big := gi.scrBig
  have l := h.lens
  have R : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s s' := ⟨fun r hr => by
    refine hpres r ?_ ?_ <;> clear * - hr <;> cases r <;> simp_all [preserved], hrd, hwr, hsp⟩
  have bl : Region.Sub (belowA s.sp (armStack code)) G.rBelow := by
    have := gi.sp176; have := ok.stack
    refine fun a ha => ?_
    have hs' := FrameStack.belowA_sub (sp := s.sp) (a := armStack code) (b := 176) (by omega_arith)
      (by rw [gi.sp]; omega_arith) a ha
    rw [gi.sp] at hs'
    show Region.Contains ⟨State.addr G.sp - 176#64, 176⟩ a 1
    have e : State.addr (G.sp - BitVec.ofNat 32 176) = State.addr G.sp - 176#64 := FrameStack.addr_sub' (by omega_arith)
    simpa only [FrameStack.belowA, e] using hs'
  refine ⟨⟨h.of_scr R (o := sA) (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (f.sub fun r hr => ?_) fun y hy => .inl (hcl y hy), x⟩, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨G.rs sA (wa G.pLen), List.mem_cons_self, by rw [GP.rPow, w8]; exact fun _ h => h⟩
    · exact ⟨G.rBelow, by simp, bl⟩
  · obtain ⟨v, -⟩ := hpost
    simp only [Proof.Dsa.ModPow.numAt, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide)] at v
    have e0 : ∀ o, State.addr (s.gpr .r0) + BitVec.ofNat 64 o = G.sa (sA + o) := fun o => by
      rw [a0]; simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e0, e0, e0, e0, pin.1, pin.2.1, pin.2.2] at v
    exact v

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: one `h` of the generator search

`gStep` (`gStep_vp`): `h`, the `pLen` bytes at `fH` of `rand`, into
array `aH`; unless `1 < h < p − 1`, nothing more; else `g = h^((p−1)/q) mod p`
by the exponentiation, and if `g > 1`, `g` big-endian at `sG` and `fG` := 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Proof.Rsa (b2n)

/-- The `h` at byte `i` of `rand`. -/
abbrev hAt (G : GP) (i : Nat) : List Byte := (G.witB.drop i).take G.pLen

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

/-- The `h` at byte `i`, as a source of a load. -/
theorem GI.hSrc (h : GI G σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.witLen) (hp : 0 < G.pLen) :
    Covers [⟨State.addr (G.wit + BitVec.ofNat 32 i), G.pLen⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨State.addr (G.wit + BitVec.ofNat 32 i), G.pLen⟩ G.rK ∧
      (G.wit + BitVec.ofNat 32 i).toNat + G.pLen ≤ 2 ^ 32 ∧
      Spec.Rsa.bytesAt s.mem (State.addr (G.wit + BitVec.ofNat 32 i)) G.pLen = hAt G i := by
  have fit := h.witFit
  obtain a : State.addr (G.wit + BitVec.ofNat 32 i) = State.addr G.wit + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain sub : Region.Sub ⟨State.addr G.wit + BitVec.ofNat 64 i, G.pLen⟩ G.rWit := Offset.sub_base _ hi
  obtain hC := h.pre.wC; rw [h.hG] at hC
  obtain e : G.witB = Spec.Rsa.bytesAt σ.mem (State.addr G.wit) G.witLen := by rw [← h.hG]; rfl
  refine ⟨Covers.left (Covers.one ⟨G.rWit, by rw [h.rd, h.pre.rd, h.hG]; simp, a ▸ Offset.contains_base _ hi
    (by omega_arith)⟩), a ▸ (hC.sub_left sub).sub_right h.kSub, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [h.keeps fit h.wit_apart hi, hAt, e]

end

/-- The stage after an `h` (`hv`), from `p` (`pv`) and `(p − 1) / q` (`ev`). -/
def gOut (c : Cfg) (G : GP) (hv pv ev : Nat) : Cfg :=
  if 1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv then
    ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1
  else c

/-- The certificates of `gStep`'s pieces that depend on the geometry. -/
structure GStepCerts (g : Geo) : Prop where
  mod : Cert7 (copyN (scr g.pLen .r0 (sA + g.powMod)) (ptr .r1 aP) g.pLen)
  base : Cert7 (copyN (scr g.pLen .r0 (sA + g.powBase)) (ptr .r1 aH) g.pLen)
  exp : Cert7 (copyN (scr g.pLen .r0 (sA + g.powExp)) (ptr .r1 aE) (4 * g.e))
  res : Cert7 (copyN (ptr .r0 aG) (scr g.pLen .r1 (sA + g.powRes)) g.pLen)
  st : Cert7 (storeBE g.pLen aG sG g.pLen)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Simplifies a stage's arrays and header words. -/
syntax "kv_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| kv_simp $[$loc]?) => `(tactic| simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, aQt, aRm, aDv, aDt,
    aX, aT, aS, aPm1, aP, aE, aH, aOne, aG, aZero, aTmp, slOdd, slLo, slHi, slG, Nat.reduceEqDiff, ↓reduceIte] $[$loc]?)

/-- `scratch` below the key working space lies in the 32-bit address space. -/
abbrev Fit (G : GP) : Prop := sK G.pLen ≤ 2 ^ 32

theorem SS.fit {σ s : State} (h : SS G σ c s) : Fit G := by
  have := h.gi.scrBig; have := h.gi.scrFit; simp only [Fit]; omega_arith

/-- A range of `scratch` through a copy to another. -/
theorem scr_keep {m m' : Mem} {a n b k : Nat} (fit : Fit G) (f : Frame [G.rs a n] m m')
    (hs : b + k ≤ a ∨ a + n ≤ b) (ha : a + n ≤ sK G.pLen) (hb : b + k ≤ sK G.pLen) :
    m'.read (G.sa b) k = m.read (G.sa b) k := by
  simp only [Fit] at fit
  exact f.read (r := G.rs b k) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)) (by omega_arith)

/-- `g` from `h` (`hv`) in range: `h ^ ((p − 1) / q) mod p`, stored if it is
above 1. The stage `c` is `c0`'s with more arrays and header words. -/
theorem gPow_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c0 : Cfg} {pv ev hv : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hHm : aH ∈ c.live) (hHv : c.A aH = hv) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hTl : aTmp ∉ c.live) (hGl : aG ∉ c0.live)
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hvlt : hv < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG)
    (eV : c.V = c0.V) (eLS : c.LS = c0.LS) (ecl : c.cl = c0.cl)
    (eA : ∀ j ∈ c0.live, j ∈ c.live ∧ c.A j = c0.A j) (ek : c0.kls = []) :
    VP (St G c X)
      (VG.Impl.Rsa.Arm.Keys.seqs [copyN (scr G.pLen .r0 (sA + g.powMod)) (ptr .r1 aP) G.pLen,
        copyN (scr G.pLen .r0 (sA + g.powBase)) (ptr .r1 aH) G.pLen,
        copyN (scr G.pLen .r0 (sA + g.powExp)) (ptr .r1 aE) (4 * g.e),
        .block (scr G.pLen .r0 sA ++ ([.movw .r1 (BitVec.ofNat 16 (wa G.pLen / 8))] : List Instr)),
        .call g.powName g.powCode,
        copyN (ptr .r0 aG) (scr G.pLen .r1 (sA + g.powRes)) G.pLen,
        VG.Impl.Rsa.Arm.Keys.seqs (ltS slG aOne aG),
        .block [.ldr .r1 .r8 slG, .cmp .r1 (.imm 0)],
        .ite .eq (.block [])
          (VG.Impl.Rsa.Arm.Keys.seqs [storeBE G.pLen aG sG G.pLen, .block (stImm fG 1)])])
      (St G (if 1 < hv ^ ev % pv then
        ({ c0 with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c0.cl }).setV fG 1 else c0) X) := by
  obtain ⟨cm, cb, ce, cr, cs⟩ := certs
  rw [hp] at cm cb ce cr cs
  rw [hpm] at cm; rw [hpb] at cb; rw [hpe] at ce; rw [hpr] at cr
  rw [hpm, hpb, hpe, hpr]
  obtain w4 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  obtain hpL : 0 < G.pLen := by omega_arith
  obtain sz : ∀ i, i ≤ 11 → sA + VG.Impl.Mont.Arm.Dynamic.slot n i + G.pLen ≤ sK G.pLen := fun i hi => by
    have := Nat.mul_le_mul_right (8 * n + 8) (show i + 1 ≤ 12 by omega_arith)
    simp only [Nat.add_mul, Nat.one_mul] at this
    simp only [contextBytes, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride, sK, wa] at hctx ⊢; omega_arith
  obtain hsK : sA ≤ sK G.pLen := by simp only [sK]; omega_arith
  obtain ap : ∀ o k, sA ≤ o → ∀ x ∈ c.cl, x ∈ c.cl ∧ Apart o k x := fun o k ho x hx =>
    ⟨hx, .inl (by have := hcl x hx; simp only [sG, sA] at *; omega_arith)⟩
  generalize hr : hv ^ ev % pv = r
  obtain rlt : r < pv := hr ▸ Nat.mod_lt _ (by omega_arith)
  -- The modulus, the base and the exponent.
  refine VP.seq ((copyOut_vp (E := fun _ => True) cm rfl hP hpL (by omega_arith) (by simpa [modS] using sz 0 (by omega_arith))
    (ap _ _ (by simp only [modS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith)) fun _ _ _ _ => trivial).mono (fun σ s h => ⟨h, trivial⟩) fun σ t h => h)
    ?_
  refine VP.seq ((copyOut_vp (E := fun m => Fit G → (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv) cb rfl hHm hpL
    (by omega_arith) (by simpa [baseS] using sz 8 (by omega_arith)) (ap _ _ (by simp only [baseS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith))
    fun m m' e f fit => by
      rw [scr_keep fit f (by simp only [modS, baseS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith) (by simpa [baseS] using sz 8 (by omega_arith))
        (by rw [hn]; simpa [modS] using sz 0 (by omega_arith))]; exact e fit).mono
    (fun σ s ⟨h, _, e⟩ => ⟨h, fun _ => by rw [hn, e, hPv, Nat.mod_eq_of_lt hplt]⟩) fun σ t h => h) ?_
  refine VP.seq ((copyOut_vp (E := fun m => Fit G → (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv ∧
      (m.read (G.sa (sA + baseS n)) (8 * n)).toNat = hv) ce rfl hE (by omega_arith)
    (by omega_arith) (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (ap _ _ (by simp only [expS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith))
    fun m m' e f fit => by
      rw [scr_keep fit f (by simp only [modS, expS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith)
          (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (by rw [hn]; simpa [modS] using sz 0 (by omega_arith)),
        scr_keep fit f (by simp only [baseS, expS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith)
          (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (by rw [hn]; simpa [baseS] using sz 8 (by omega_arith))]
      exact e fit).mono
    (fun σ s ⟨h, e1, e⟩ => ⟨h, fun fit => ⟨e1 fit, by rw [hn, e, hHv, Nat.mod_eq_of_lt hvlt]⟩⟩) fun σ t h => h) ?_
  -- The exponentiation.
  refine VP.assoc (VP.seq ((powCall_vp (X := X) (hv := hv) (cl' := c.cl) ok rfl hctx hpodd hp1
    (fun x hx => ap _ _ (Nat.le_refl _) x hx)).mono (fun σ s ⟨h, e1, e⟩ =>
      ⟨h, (e1 h.1.fit).1, (e1 h.1.fit).2, by
        rw [e, hEv, Nat.mod_eq_of_lt (by rwa [show 8 * (4 * g.e) = 32 * g.e by omega_arith])]⟩) fun σ t h => h) ?_)
  -- g into its array.
  refine VP.seq ((copyIn_vp (v := r) cr rfl (by decide) (by omega_arith) (by simpa [resS] using sz 9 (by omega_arith))).mono
    (fun σ s ⟨h, e⟩ => ⟨h, by rw [← hn, e, hr]⟩) fun σ t h => h) ?_
  -- 1 < g.
  obtain b2le : ∀ b : Bool, b2n b ≤ 1 := fun b => by cases b <;> decide
  obtain vG : KU c.A aG r aG = r := by kv_simp
  obtain vO' : KU c.A aG r aOne = 1 := by kv_simp; exact hOv
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aOne aG), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slG]), by kernel_rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  refine VP.seq (slotCmp_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (.block [.ldr .r1 .r8 slG, .cmp .r1 (.imm 0)]), by kernel_rfl⟩ (by simp)
      (by kv_simp; exact b2le _)) ?_
  obtain kG : ∀ j ∈ c0.live, j ∈ aG :: c.live ∧ KU c.A aG r j = c0.A j := fun j hj => by
    have : j ≠ aG := fun e => hGl (e ▸ hj)
    refine ⟨List.mem_cons_of_mem _ (eA j hj).1, ?_⟩
    simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]; exact (eA j hj).2
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- g ≤ 1: nothing stored.
    refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    obtain nr : ¬1 < r := by
      intro h1; simp only [Option.some.injEq, decide_eq_true_eq] at z
      kv_simp at z hOv; simp [hOv, b2n, h1] at z
    simp only [nr, ↓reduceIte]
    exact h.mono (fun o ho => ⟨eLS ▸ ho, by rw [eV]⟩) (fun y hy => ecl ▸ hy) kG
      (fun d hd => by rw [ek] at hd; simp at hd)
  · -- g > 1: stored, and fG := 1.
    by_cases hr1 : 1 < r
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not] at z
      kv_simp at z hOv; simp [hOv, b2n, hr1] at z
    refine VP.seq ((storeBE_vp (cl' := c.cl) cs rfl (by simp) hpL (by omega_arith)
      (by simp only [sG, sK, sA, wa]; omega_arith) fun x hx => ⟨by exact hx, .inl (hcl x hx)⟩).mono
      (fun σ s h => h.1.1) fun σ t h => h) ?_
    simp only [hr1, ↓reduceIte]
    refine stImm_vp (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.2⟩
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun j hj => kG j hj) (fun d hd => by rw [ek] at hd; simp at hd)
    · simp only [List.mem_cons] at ho ⊢
      refine ⟨ho.imp id (eLS ▸ ·), ?_⟩
      simp only [upd]; split
      · rfl
      · rw [eV]
    · simp only [List.mem_cons] at hy ⊢
      rcases hy with rfl | hy
      · left; rw [vG, Nat.mod_eq_of_lt (by omega_arith)]
      · right; exact ecl ▸ hy

theorem gStep_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {pv ev i : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG)
    (hH : fH ∈ c.LS) (hHv : c.V fH = G.wit + BitVec.ofNat 32 i) (hi : i + G.pLen ≤ G.witLen)
    (hwl : G.witB.length = G.witLen) :
    VP (St G c X) g.gStep (St G (gOut c G (Spec.Dsa.decodeBE (hAt G i)) pv ev) X) := by
  obtain w4 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have hsG : sG = 1728 := rfl
  have hAv : sA = 4096 := rfl
  obtain hpL : 0 < G.pLen := by omega_arith
  generalize hhv : Spec.Dsa.decodeBE (hAt G i) = hv
  obtain hal : (hAt G i).length = G.pLen := by
    simp only [hAt, List.length_take, List.length_drop, hwl]; omega_arith
  obtain hvlt : hv < 2 ^ (8 * G.pLen) := by
    rw [← hhv]; have := VG.Proof.Dsa.decodeBE_lt (hAt G i)
    rwa [hal, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  -- Back to `c`: its arrays kept, nothing else.
  obtain back : ∀ (c' : Cfg) σ s, SS G σ c' s → c'.V = c.V → c'.LS = c.LS → c'.cl = c.cl →
      (∀ j ∈ c.live, j ∈ c'.live ∧ c'.A j = c.A j) → SS G σ c s := fun c' σ s h e1 e2 e3 e4 =>
    h.mono (fun o ho => ⟨e2 ▸ ho, by rw [e1]⟩) (fun y hy => e3 ▸ hy) e4 (fun d hd => by rw [hkls] at hd; simp at hd)
  unfold Geo.gStep
  rw [hp]
  -- h.
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r4 = G.wit + BitVec.ofNat 32 i)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hH).trans hHv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r4]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r4 = G.wit + BitVec.ofNat 32 i) ∧
      s.gpr .r6 = BitVec.ofNat 32 G.pLen)
    (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block [.movw .r6 (BitVec.ofNat 16 1)]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨⟨h, x⟩, r4⟩ => wp_movw fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r6]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r4]⟩,
          by rw [u.gpr, setWidth_ofNat16 (by omega_arith)]⟩) ?_
  refine VP.seq ((loadAt_vp (c := c) (X := X) (src := G.wit + BitVec.ofNat 32 i) (bs := hAt G i)
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.CrtValues.load aH), by kernel_rfl⟩ (by decide) hal hpL (by omega_arith)
    fun σ s ⟨h, _⟩ => h.gi.hSrc hi hpL).mono (fun σ s ⟨⟨h, r4⟩, r6⟩ => ⟨h, r4, r6⟩) fun _ _ h => h.1) ?_
  rw [hhv]
  -- 1 < h, h < p − 1 and both.
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aOne aH), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slLo]), by kernel_rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aH aPm1), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slHi]), by kernel_rfl⟩
    (by simp) (by simp [hM]) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  obtain b2le : ∀ b : Bool, b2n b ≤ 1 := fun b => by cases b <;> decide
  obtain b2one : ∀ p : Prop, [Decidable p] → (b2n (decide p) = 1 ↔ p) := fun p _ => by
    by_cases hp' : p <;> simp [b2n, hp']
  refine VP.seq (andCmp_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (.block (VG.Impl.Rsa.Arm.Keys.andS slLo slLo slHi ++ [.ldr .r1 .r8 slLo, .cmp .r1 (.imm 0)])), by kernel_rfl⟩
    (by decide) (by simp) (by simp) (by kv_simp; exact b2le _) (by kv_simp; exact b2le _)) ?_
  obtain vO : KU c.A aH hv aOne = 1 := by kv_simp; exact hOv
  obtain vH : KU c.A aH hv aH = hv := by kv_simp
  obtain vM : KU c.A aH hv aPm1 = pv - 1 := by kv_simp; exact hMv
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- Out of range: nothing more.
    refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    obtain nr : ¬(1 < hv ∧ hv < pv - 1) := by
      intro hr; simp only [Option.some.injEq, decide_eq_true_eq] at z
      kv_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact z ⟨(b2one _).mpr hr.1, (b2one _).mpr hr.2⟩
    obtain nc : ¬(1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv) := fun hc => nr ⟨hc.1, hc.2.1⟩
    simp only [gOut, nc, ↓reduceIte]
    refine back _ σ s h rfl rfl rfl fun j hj => ⟨by simp [hj], ?_⟩
    have : j ≠ aH := fun e => hHl (e ▸ hj)
    simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]
  · by_cases hr : 1 < hv ∧ hv < pv - 1
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not, not_not] at z
      kv_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact hr ⟨(b2one _).mp z.1, (b2one _).mp z.2⟩
    obtain eq : gOut c G hv pv ev = if 1 < hv ^ ev % pv then
        ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1 else c := by
      simp only [gOut, hr, true_and]
    rw [eq]
    obtain kH : ∀ j ∈ c.live, j ∈ aH :: c.live ∧ KU c.A aH hv j = c.A j := fun j hj => by
      have : j ≠ aH := fun e => hHl (e ▸ hj)
      exact ⟨List.mem_cons_of_mem _ hj, by simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]⟩
    exact (gPow_vp (c := { c with A := KU c.A aH hv, live := aH :: c.live }) certs ok hp hn hpm hpb hpe hpr
      hctx he4 he0 (List.mem_cons_of_mem _ hP) ((kH _ hP).2.trans hPv) (List.mem_cons_of_mem _ hE)
      ((kH _ hE).2.trans hEv) List.mem_cons_self (by kv_simp) (List.mem_cons_of_mem _ hO) ((kH _ hO).2.trans hOv)
      (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩) hGl hpodd hp1 hplt hev hvlt hcl
      rfl rfl rfl kH hkls).mono
      (fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy)
        (fun j hj => ⟨hj, rfl⟩) (fun d hd => by simp only [hkls, List.not_mem_nil] at hd), x⟩) fun _ _ h => h

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: the search for g

`gPart_vp`: the window of `rand` at `w` (`fHs`, of `HL` octets, `fHsLen`) read
candidate by candidate, `gStep` on each, until one gives a g above 1 (`fG`
:= 1, g at `sG`) or fewer than `p_len` octets are left (`fG` := 2), as
`Spec.Dsa.generator` searches its candidates; `fH` then points past the
candidates read (`generatorCount`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)


/-- The window's octets. -/
abbrev hsW (G : GP) (w HL : Nat) : List Byte := (G.witB.drop w).take HL

/-- The window's candidates from the `k`-th. -/
abbrev gCands (G : GP) (w HL k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((hsW G w HL).drop (k * G.pLen))).map Spec.Dsa.decodeBE

/-- The search's frame words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (w HL k : Nat) : Cfg :=
  ((c.setV fH (G.wit + BitVec.ofNat 32 (w + k * G.pLen))).setV fHLeft (BitVec.ofNat 32 (HL - k * G.pLen))).setV fG 4

/-- Whether the h at byte `i` of `rand` gives a g above 1. -/
abbrev gOk (G : GP) (pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (hAt G i) ∧ Spec.Dsa.decodeBE (hAt G i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (hAt G i) ^ ev % pv

/-- The search's iterations from the `k`-th h, with `m` left. -/
def gCount (G : GP) (w pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G pv ev (w + k * G.pLen) then k + 1 else gCount G w pv ev m (k + 1)

theorem gCount_gt (G : GP) (w pv ev : Nat) : ∀ m k, k < gCount G w pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega_arith
    · exact Nat.lt_of_succ_lt (gCount_gt G w pv ev m (k + 1))

/-- The generator the spec finds from the `k`-th h. -/
abbrev gRes (G : GP) (w HL pv qv k : Nat) : Option Nat := Spec.Dsa.generator pv qv (gCands G w HL k)

/-- The candidates the spec reads from the `k`-th h. -/
abbrev gNum (G : GP) (w HL pv qv k : Nat) : Nat :=
  VG.Proof.Dsa.Generation.generatorCount pv qv (gCands G w HL k)

/-- The stage after the search: `fH` past the candidates read. -/
def gFin (c : Cfg) (G : GP) (w HL pv qv : Nat) : Cfg :=
  match gRes G w HL pv qv 0 with
  | some g => ((({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 32 (w + gNum G w HL pv qv 0 * G.pLen)))
  | none => (c.setV fG 2).setV fH (G.wit + BitVec.ofNat 32 (w + gNum G w HL pv qv 0 * G.pLen))

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (w HL pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ HL / G.pLen ∧ gCount G w pv ev (HL / G.pLen - (N - r)) (N - r) = N ∧
    gRes G w HL pv qv (N - r) = gRes G w HL pv qv 0 ∧
    N - r + gNum G w HL pv qv (N - r) = gNum G w HL pv qv 0) ∧ St G (gCfg c G w HL (N - r)) X σ s

/-- A candidate of the window is the `h` at its place in `rand`. -/
theorem hsW_take {G : GP} {w HL i : Nat} (hi : i + G.pLen ≤ HL) :
    ((hsW G w HL).drop i).take G.pLen = hAt G (w + i) := by
  simp only [hsW, hAt, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega_using [hi]), Nat.add_comm]

theorem hsW_length {G : GP} {w HL : Nat} (hw : w + HL ≤ G.witLen) (hl : G.witB.length = G.witLen) :
    (hsW G w HL).length = HL := by
  simp only [hsW, List.length_take, List.length_drop, hl]; omega_using [hw]

section
variable {G : GP} {X : State → Prop}

/-- The next `h`: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) :
    VP (St G d X) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r1 fH],
        .block [.movw .r2 (BitVec.ofNat 16 G.pLen), .dp .add .r1 .r1 (.reg .r2)],
        .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 32 G.pLen)) X) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = d.V fH)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => h.1.slotV hH)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r1 = d.V fH + BitVec.ofNat 32 G.pLen) ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.movw .r2 (BitVec.ofNat 16 1), .dp .add .r1 .r1 (.reg .r2)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_movw fun t u => wp_dp (op2_reg _ _) fun t' u' => WP.block_nil ?_) ?_
  · have l := h.lens
    obtain r2 : t.gpr .r2 = BitVec.ofNat 32 G.pLen := by rw [u.gpr, setWidth_ofNat16 (by omega_arith)]
    refine ⟨⟨⟨h.of_rest ((u.rest (ws := [.r1, .r2]) (by simp)).trans (u'.rest (ws := [.r1, .r2]) (by simp)))
      (by rw [u'.mem, u.mem]), x⟩, ?_⟩, by rw [u'.other _ (by decide), r2]⟩
    rw [u'.gpr, dpVal, u.other _ (by decide), r1, r2]
  obtain hHL : fHLeft ∈ (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨h, x⟩, r1⟩, r2⟩ h' R => ⟨⟨r1 ▸ h', x⟩, by rw [R.gpr _ (by decide), r2]⟩) ?_
  refine VP.seq (G := fun σ s => (St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen) ∧ s.gpr .r1 = d.V fHLeft)
    (ld_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => (h.1.1.slotV hHL).trans (by simp [upd, fHLeft, fH]))
      fun σ s t ⟨⟨h, x⟩, r2⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r2]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r1 = d.V fHLeft - BitVec.ofNat 32 G.pLen)
    (VP.taint [.r1, .r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r2])
      (.block [.dp .sub .r1 .r1 (.reg .r2)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2, h₂.2]
        · rw [h₁.1.2, h₂.1.2])
      fun σ s ⟨⟨⟨h, x⟩, r2⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1, r2]⟩) ?_
  exact st_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩

/-- The search's frame words agree with `c`'s but for `fH`, `fHLeft` and
`fG`, with `fG` and `fH` as the search leaves them. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 32} {LS : List Nat}
    {v x : BitVec 32} (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o)
    (hG : fG ∈ LS) (hVG : V fG = v) (hH : fH ∈ LS) (hVH : V fH = x) :
    ∀ o ∈ fH :: fG :: c.LS, o ∈ LS ∧ V o = upd (upd c.V fG v) fH x o := by
  intro o ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · exact ⟨hH, by rw [hVH, upd_self]⟩
  · exact ⟨hG, by rw [hVG, upd_ne _ _ (by decide), upd_self]⟩
  · refine ⟨hLS o ho, ?_⟩
    obtain e1 : o ≠ fH := fun h => hfH (h ▸ ho)
    by_cases e : o = fG
    · subst e; rw [hVG, upd_ne _ _ (by decide), upd_self]
    · rw [upd_ne _ _ e1, upd_ne _ _ e, hV o e1 (fun h => hfL (h ▸ ho)) e]

theorem gBody_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv N w HL : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hw : w + HL ≤ G.witLen) (hwl : G.witB.length = G.witLen)
    (h32 : HL < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G w HL pv ev qv N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r0 fHLeft],
        .block (([.movw .r1 (BitVec.ofNat 16 g.pLen)] : List Instr) ++ less),
        .ite .eq (.block (stImm fG 2)) (VG.Impl.Rsa.Arm.Keys.seqs [g.gStep, .block [ld .r1 fH],
          .block [.movw .r2 (BitVec.ofNat 16 g.pLen), .dp .add .r1 .r1 (.reg .r2)],
          .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧ (r = 0 → St G (gFin c G w HL pv qv) X σ s) ∧
        (0 < r → gInv c G w HL pv ev qv N X r σ s)) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hk, hc, hres, hnum⟩ => ?_
  obtain hpL : 0 < G.pLen := by omega_arith
  obtain hp16 : G.pLen < 2 ^ 16 := by omega_arith
  generalize hMM : HL / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hnum
  obtain kL : ∀ j, j ≤ M → j * G.pLen ≤ HL := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  obtain hlen := hsW_length (G := G) hw hwl
  rw [hp]
  -- Whether an h is left.
  refine VP.assoc (VP.seq (G := fun σ s => St G (gCfg c G w HL k) X σ s ∧
      isa.eval .eq s = some (decide (HL - k * G.pLen < G.pLen)))
    (ltF_vp (c := fun _ => gCfg c G w HL k) (x := BitVec.ofNat 32 (HL - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) hp16 (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]⟩) ?_)
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    obtain hi : k * G.pLen + G.pLen ≤ HL := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    obtain e0 : decide (HL - k * G.pLen < G.pLen) = false := decide_eq_false (by omega_arith)
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega_arith⟩
    rw [hm] at hc; simp only [gCount] at hc
    obtain hbl : G.pLen ≤ ((hsW G w HL).drop (k * G.pLen)).length := by
      simp only [List.length_drop, hlen]; omega_arith
    obtain hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hbl
    obtain cstep := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hbl
    rw [hsW_take hi, List.drop_drop] at hstep cstep
    simp only [VG.Proof.Dsa.powMod_eq, ← hev'] at hstep cstep
    obtain stepVP := gStep_vp (c := gCfg c G w HL k) (X := X) (i := w + k * G.pLen) certs ok hp hlq hn hpm hpb hpe
      hpr hctx he4 he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd hp1 hplt hev hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) (by omega_arith) hwl
    obtain notLeft : ∀ σ s, ¬((St G (gCfg c G w HL k) X σ s ∧
        isa.eval .eq s = some (decide (HL - k * G.pLen < G.pLen))) ∧
        isa.eval .eq s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    obtain eH : G.wit + BitVec.ofNat 32 (w + k * G.pLen) + BitVec.ofNat 32 G.pLen =
        G.wit + BitVec.ofNat 32 (w + (k + 1) * G.pLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
    by_cases hok : gOk G pv ev (w + k * G.pLen)
    · -- It gives g: done.
      obtain r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega_arith
      subst r0
      obtain some0 : gRes G w HL pv qv 0 = some (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv) := by
        rw [← hres, gRes, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      obtain num0 : gNum G w HL pv qv 0 = k + 1 := by
        rw [← hnum, gNum, cstep, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      obtain hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev =
          ({ gCfg c G w HL k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G w HL k).cl }).setV fG 1 := by
        simp only [gOut]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      simp only [gFin, some0, num0]
      exact (h.of_rest R mm).mono (gV hfH hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
        (by simp) (by simp [upd, fH, fHLeft, fG]) (by simp) (by simp [upd, fH, fHLeft, fG, eH]))
        (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · -- It does not: the next h.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      obtain rpos : 0 < r := by have := gCount_gt G w pv ev m (k + 1); omega_arith
      obtain hNr : N - r = k + 1 := by omega_arith
      obtain hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev =
          gCfg c G w HL k := by
        simp only [gOut]; exact ite_eq_right_of_eq_false _ _ (eq_false hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      obtain eL : BitVec.ofNat 32 (HL - k * G.pLen) - BitVec.ofNat 32 G.pLen =
          BitVec.ofNat 32 (HL - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega_arith
      refine cmpF_vp (x := BitVec.ofNat 32 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega_arith, by omega_arith, by rw [hMM, show M - (k + 1) = m by omega_arith]; exact hc, ?_, ?_⟩,
        ?_, x⟩
      · rw [← hres]; simp only [gRes, gCands]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · rw [← hnum]; simp only [gNum, gCands]
        rw [cstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]; omega_arith
      · refine (h.of_rest R mm).mono (fun o ho => ⟨?_, ?_⟩) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
          (fun d hd => ⟨hd, rfl⟩)
        · simp only [List.mem_cons] at ho ⊢
          rcases ho with h' | h' | h' | h' <;> simp [h']
        · simp only [upd]
          by_cases a : o = fHLeft
          · subst a; simp [eL, fHLeft, fG]
          · by_cases b : o = fH
            · subst b; simp [eH, fH, fHLeft, fG]
            · simp [a, b]
  · -- Fewer than `p_len` octets left: `fG` := 2.
    obtain hkM' : k = M := by omega_arith
    subst hkM'
    obtain r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega_arith
    subst r0
    obtain hz : decide (HL - k * G.pLen < G.pLen) = true := by
      refine decide_eq_true ?_
      rw [← hMM, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]; exact Nat.mod_lt _ hpL
    obtain hsh : ((hsW G w HL).drop (k * G.pLen)).length < G.pLen := by
      simp only [List.length_drop, hlen]; exact of_decide_eq_true hz
    obtain none0 : gRes G w HL pv qv 0 = none := by
      rw [← hres]
      show Spec.Dsa.generator pv qv ((Spec.Dsa.generationChunks _ _).map _) = none
      rw [VG.Proof.Dsa.Generation.generationChunks_done hsh]
      rfl
    obtain num0 : gNum G w HL pv qv 0 = k := by
      rw [← hnum, gNum, VG.Proof.Dsa.Generation.generatorCount_chunks_done hsh, Nat.add_zero]
    refine VP.seq (G := St G ((gCfg c G w HL k).setV fG (BitVec.ofNat 32 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G w HL k) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G w HL k).setV fG (BitVec.ofNat 32 2)) (x := BitVec.ofNat 32 2)
      (fun σ s h => h.1) (by decide)
      (by decide) (by decide) (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    simp only [gFin, none0, num0]
    exact (h.of_rest R mm).mono (gV hfH hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd]) (by simp) (by simp [upd, fH, fHLeft, fG])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)

/-- The search for g over the window of `HL` octets at `w`. -/
theorem gPart_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv w HL : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hS : fHs ∈ c.LS) (hSv : c.V fHs = G.wit + BitVec.ofNat 32 w)
    (hL : fHsLen ∈ c.LS) (hLv : c.V fHsLen = BitVec.ofNat 32 HL) (hw : w + HL ≤ G.witLen)
    (hwl : G.witB.length = G.witLen) (h32 : HL < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS)
    (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G w HL pv qv) X) := by
  unfold Geo.gPart
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r1 = G.wit + BitVec.ofNat 32 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hS).trans hSv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  obtain hHs : fHsLen ∈ (c.setV fH (G.wit + BitVec.ofNat 32 w)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := St G (c.setV fH (G.wit + BitVec.ofNat 32 w)) X)
    (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  refine VP.seq (G := fun σ s => St G (c.setV fH (G.wit + BitVec.ofNat 32 w)) X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 HL)
    (ld_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 32 w)) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hHs).trans ((upd_ne (o := fH) _ (G.wit + BitVec.ofNat 32 w) (by decide)).trans hLv))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := St G ((c.setV fH (G.wit + BitVec.ofNat 32 w)).setV fHLeft (BitVec.ofNat 32 HL)) X)
    (st_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 32 w)) (fun σ s h => h.1.1) (by decide)
      (varOk_of (by decide)) fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  obtain hN := gCount_gt G w pv ev (HL / G.pLen) 0
  generalize hNN : gCount G w pv ev (HL / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G w HL pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH (G.wit + BitVec.ofNat 32 w)).setV fHLeft (BitVec.ofNat 32 HL))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self],
          by rw [Nat.sub_self, Nat.zero_add]⟩, by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega_arith]
  exact VP.loop (I := gInv c G w HL pv ev qv (N - 1 + 1) X)
    (gBody_vp certs ok hp hlq hn hpm hpb hpe hpr hctx he4 he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd
      hp1 hplt hev hcl hw hwl h32 hfH hfL hev') _

end

end VG.Proof.Dsa.Arm.Gen
