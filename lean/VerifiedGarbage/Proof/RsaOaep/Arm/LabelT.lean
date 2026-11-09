module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP on ARMv7: the label's hash with a table

`labelT_vp`: with the label in the arguments `j` (its address) and `j + 1`
(its length), a range of bytes the body may read whose bytes do not change,
`hashLabelT` writes `H(label)` to `scratch + o`, with the hash function that
of the table at `p`, whose address is in the slot `sTab`: each of its calls
through the table (`tloadG_vp`, `tcallIG_vp`, `tcallKG_vp`, as their MGF1
versions) runs as the function's own, in every run at the same address
(`TabFacts`). `byLen_vp`: the branch on the digest length in `r1`, which
both runs have the same.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32}

section TCall

variable (hg : Geo L scr) {g : OHash} {f : Fns} {p ai au af : BitVec 32}
  (tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (tA p o) 4) {Inv : State → Mem → Prop}
  (hS : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p) (hT : ∀ σ m, Inv σ m → TabFacts g.H f p ai au af σ)
include hg tbl hS hT

/-- The table's word `k`, `a` in every run, into `r4`, from a stage with
`Ctx`, what the caller keeps (`Inv`: the table's address in its slot, and
what the table holds in every run) and `X`, which a write of `r4` keeps. -/
theorem tloadG_vp {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v)) {k : Nat}
    (hk3 : k < 3) {a : BitVec 32} (ha : ∀ σ, TabFacts g.H f p ai au af σ → σ.mem.readW (tA p (4 * k)) 32 = a) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) (.block (tload k))
      (fun σ s => ((Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) ∧ s.gpr .r4 = a) := by
  have hk : 4 * k + 4 ≤ 20 := by omega
  obtain ⟨tR, tRo, tC⟩ := tbl
  let F : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms
  have keepF : ∀ σ s v, F σ s → F σ (s.setReg .r4 v) := fun σ s v ⟨⟨hc, hm, hx⟩, sy⟩ =>
    ⟨⟨Ctx.setReg_iff.mpr hc, hm, hX σ s v hx⟩, sy⟩
  show VP F (.block ([Impl.RsaPss.Arm.ld .r4 sTab] ++ [.ldr .r4 .r4 (4 * k)])) (fun σ s => F σ s ∧ s.gpr .r4 = a)
  refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .r4 = p)
    (VP.ldrSp (c := [(.r4, sTab)]) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s hs => WP.mono (wp_ldS hg hs.1.1 (r := .r4) (by decide) (by decide)) fun t e => ?_)
    (VP.taint [.r4] (tword_cert hk3) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · subst e
    exact ⟨keepF σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]; exact hS σ _ hs.1.2.1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨hF, hsi⟩ := hs
    have T := hT σ _ hF.1.2.1
    refine WP.mono (wp_ldrT (by omega) hsi (St_roR hF.1.1.st tRo (tC _ hk))
      ((St_roW hF.1.1.st tRo (tC _ hk)).trans (ha σ T))) fun t e => ?_
    subst e
    exact ⟨keepF σ s _ hF, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The call of `init` through the table, as the call of `g`'s. -/
theorem tcallIG_vp (fne : f.init ≠ []) {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) (.call g.H.initN g.H.initC) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) (callInit f) G :=
  tcall_vp fne (tloadG_vp hg tbl hS hT hX (k := 0) (by decide) (a := ai) fun σ T => T.mem.1.trans T.ai)
    (fun σ s ⟨⟨hF, sy⟩, hsi⟩ => by
      have T := hT σ _ hF.2.1
      show f.init.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .r4).setWidth 64) = _
      rw [hsi, sy, ← T.ai]; exact T.ok.i)
    (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (h.mono (fun _ _ hh => hh.1) fun _ _ hh => hh)

/-- The call of the table's function `k`, among `ts`, in a frame pushing
`rs`, as the call of `n`, at `a` in every run, in that frame. -/
theorem tcallKG_vp {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v)) {k : Nat}
    (hk3 : k < 3) {ts : List (String × Prog isa)} {rs : List Reg} {m : Nat} {n : String} {cn : Prog isa}
    {a : BitVec 32} (hne : ts ≠ [])
    (ha : ∀ σ, TabFacts g.H f p ai au af σ →
      σ.mem.readW (tA p (4 * k)) 32 = a ∧ σ.syms n = a ∧
        ts.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms n).setWidth 64) = some (n, cn))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms)
      (.frame (.push rs) (.call n cn) (.pop .r1 m)) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) (tcallF k ts rs m) G :=
  tcallF_vp hne (tloadG_vp hg tbl hS hT hX hk3 (a := a) fun σ T => (ha σ T).1)
    (fun σ s ⟨⟨hF, sy⟩, hsi⟩ => by
      have T := hT σ _ hF.2.1
      obtain ⟨-, hn, hf⟩ := ha σ T
      show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .r4).setWidth 64) = _
      rw [hsi, sy, ← hn]; exact hf)
    (fun _ _ _ _ h₁ h₂ => ⟨h₁.2.trans h₂.2.symm, h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm⟩)
    (h.mono (fun _ _ hh => hh.1) fun _ _ hh => hh)

end TCall

/-- The label's hash, with the hash function `h` of the table at `p`. -/
theorem labelT_vp (hg : Geo L scr) (h : OHash) {f : Fns} {p ai au af : BitVec 32}
    (tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (tA p o) 4)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) {j o ll : Nat} {lab : BitVec 32} (hj : j + 1 < L.argv.length)
    (hj4 : arg (j + 1) < 4096) (hj4' : arg j < 4096)
    (hlab : L.argv.getD j 0 = lab) (hll : L.argv.getD (j + 1) 0 = BitVec.ofNat 32 ll)
    (hb : RBuf L lab ll) (dS : Region.Disjoint ⟨State.addr lab, ll⟩ (sR scr oSt h.H.S))
    (dW : Region.Disjoint ⟨State.addr lab, ll⟩ (sR scr oW h.ok.Wb))
    (dL : Region.Disjoint ⟨State.addr lab, ll⟩ L.LOW)
    (ho1 : oSt + 256 ≤ o) (ho2 : o + 64 ≤ oW) {labB : State → List Byte}
    (hbytes : ∀ σ s, Ctx L scr σ s → Spec.Sha256.bytesAt s.mem (State.addr lab) ll = labB σ)
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' → Inv σ m')
    (hS : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p) (hT : ∀ σ m, Inv σ m → TabFacts h.H f p ai au af σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem) ∧ s.syms = σ.syms)
      (hashLabelT f j o)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.H.D, s.mem (sa scr (o + i)) = (h.G.hash (labB σ)).getD i 0) ∧ s.syms = σ.syms) := by
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.DF
  have hll32 : ll < 2 ^ 32 := hb.n32
  have ofr : ∀ m m', Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW] m m' →
      Frame [sR scr oSt h.H.S, sR scr oW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' :=
    fun _ _ f => f.mono (by simp)
  show VP _ (.seq (.block initArgs) (.seq (callInit f) (.seq (.block (updLabArgs j)) (.seq (callUpd f)
    (.seq (.block (finLabArgs j o)) (.seq (.block toR12) (callFin f))))))) _
  -- `init`.
  refine VP.seq (VP.syms (initArgs_vp hg)) (VP.seq (tcallIG_vp hg tbl hS hT fne.1
    (X := fun _ s => s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
    (fun _ s v h => by simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h)
    ((VP.syms (initCall_vp hg h.H h.ok (Inv := Inv) fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp)))).mono
      (fun σ s ⟨⟨hc, hm, hb⟩, sy⟩ => ⟨⟨hc, hm, hb⟩, sy⟩) fun _ _ h => h)) ?_)
  -- `update`'s arguments.
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (State.addr lab) ll = labB σ ∧
      UArgs scr lab ll 0 s) ∧ s.syms = σ.syms)
    (VP.syms (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, hi, rp⟩ => ?_)) ?_
  · obtain ⟨a1, r1, v1⟩ := argG hg hc.st (j := j) (by omega)
    obtain ⟨a2, r2, v2⟩ := argG hg hc.st (j := j + 1) hj
    rw [hlab] at v1
    rw [hll] at v2
    have hw : WP isa (.block (updLabArgs j)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        UArgs scr lab ll 0 t := by
      prun [updLabArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a1, r1, v1, a2, r2, v2, hj4, hj4',
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide)]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ =>
      ⟨hc.regs rd wr sp m, m ▸ hi, m ▸ rp, rfl, hbytes σ t (hc.regs rd wr sp m), u⟩
  -- `update` with the label.
  refine VP.seq (tcallKG_vp hg tbl hS hT (X := fun σ s => h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (State.addr lab) ll = labB σ ∧ UArgs scr lab ll 0 s)
    (fun _ _ v ⟨r, l, b, ua⟩ => ⟨r, l, b, ua.r4 v⟩) (k := 1) (by decide) fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩)
    (VP.syms (upd_vp hg h.H h.ok (msg := fun _ => []) (dat := labB) (c := 0) (Inv := Inv) hb dS dW dL (by decide)
      fun σ m m' hm hf => hI σ m m' hm (ofr _ _ hf)))) ?_
  -- `finalize`'s arguments.
  refine VP.seq (F := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ)) ∧
      s.syms = σ.syms)
    (G := fun σ s => ((Ctx L scr σ s ∧ Inv σ s.mem ∧
      h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ)) ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
      s.gpr .r1 = scr + BitVec.ofNat 32 o ∧ s.gpr .r10 = scr + BitVec.ofNat 32 oW ∧
      s.gpr .r2 = BitVec.ofNat 32 ll ∧ s.gpr .r3 = 0) ∧ s.syms = σ.syms)
    (VP.syms (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, hi, rp⟩ => ?_)) ?_
  · obtain ⟨a2, r2, v2⟩ := argG hg hc.st (j := j + 1) hj
    rw [hll] at v2
    have hw : WP isa (.block (finLabArgs j o)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 o ∧
        t.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ t.gpr .r2 = BitVec.ofNat 32 ll ∧ t.gpr .r3 = 0 := by
      prun [finLabArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a2, r2, v2, hj4,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
        movw_val (show o < 2 ^ 16 by oomega)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, r10, r2, r3⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hi, m ▸ rp⟩, r0, r1,
      r10, r2, r3⟩
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s) ∧ s.syms = σ.syms)
    ((VP.syms (toR12_vp (fun σ s hh => hh.2.2.2.1) fun σ s v hh => ?_)).mono (fun _ _ hh => hh)
    fun σ s ⟨⟨⟨⟨hc, hi, rp⟩, r0, r1, _, r2, r3⟩, r12⟩, sy⟩ => ⟨⟨hc, hi, rp, by rw [List.nil_append, ← hbytes σ s hc,
      Spec.Sha256.bytesAt, List.length_map, List.length_range], r0, r1, r12, r2, r3⟩, sy⟩) ?_
  · obtain ⟨⟨hc, hi, rp⟩, r0, r1, r10, r2, r3⟩ := hh
    have e : ∀ r, r ≠ .r12 → (s.setReg .r12 v).gpr r = s.gpr r := fun r hr => by
      simp only [VG.Arm.RegUpd.gpr_setReg, hr, ite_false]
    exact ⟨⟨Ctx.setReg_iff.mpr hc, hi, rp⟩, by rw [e _ (by decide), r0], by rw [e _ (by decide), r1],
      by rw [e _ (by decide), r10], by rw [e _ (by decide), r2], by rw [e _ (by decide), r3]⟩
  -- `finalize`.
  have hfin := tcallKG_vp hg tbl hS hT (X := fun σ s => h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s)
    (fun _ _ v ⟨r, l, fa⟩ => ⟨r, l, fa.r4 v⟩) (k := 2) (by decide) fne.2.2 (a := af)
    (fun σ T => ⟨T.mem.2.2.trans T.af, T.af, T.ok.f⟩)
    (VP.syms (fin_vp hg h.H h.ok (o := o) (c := ll) (msg := fun σ => [] ++ labB σ) (Inv := Inv) (.inr (by omega))
      (.inl (by omega)) (by oomega) hll32 fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))))
  refine hfin.mono (fun _ _ hh => hh) ?_
  rintro σ s ⟨⟨hc, hi, hd⟩, sy⟩
  refine ⟨⟨hc, hi, fun i hi' => ?_⟩, sy⟩
  have e := congrArg (fun l => l.getD i 0) hd
  simp only [List.nil_append] at e
  rw [h.hash, ← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi', Spec.Sha256.bytesAt,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The branch on the digest length -/

theorem ofNat_sub_beq32 {j N : Nat} (hj : j < 2 ^ 32) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 32 j - BitVec.ofNat 32 N == 0) = decide (j = N) := by
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 32 j = BitVec.ofNat 32 N := by bv_omega
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN] at this

theorem wp_cmpR1 {s : State} {v : BitVec 32} (he : encodable v = true) :
    WP isa (.block [.cmp .r1 (.imm v)]) s fun t => t = subFlags s (s.gpr .r1) v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, Op2.eval, he, ↓reduceIte, Option.map_some, runStep_some, runBlock_nil]
  simp

/-- `byLen` from stages with the digest length `D` in `r1`, which a `cmp`
keeps: the branch of `D`. -/
theorem byLen_vp {F G : State → State → Prop} {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 32)
    (h1 : ∀ σ s, F σ s → s.gpr .r1 = BitVec.ofNat 32 D) (hst : ∀ σ s v, F σ s → F σ (subFlags s (s.gpr .r1) v))
    (hb : VP F (b D) G) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 2 ^ 32 ∧ encodable (BitVec.ofNat 32 x) = true ∧
      ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.cmp .r1 (.imm (BitVec.ofNat 32 x))]) hc).isSome
        = true) → VP F (byLen b ds) G
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, hen, htx⟩ := hx x (List.mem_cons_self ..)
    refine VP.seq (G := fun σ s => F σ s ∧ isa.eval .eq s = some (decide (D = x)))
      (VP.taint [] htx (fun _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) fun σ s hs =>
        WP.mono (wp_cmpR1 hen) fun t e => ?_) ?_
    · subst e
      refine ⟨hst σ s _ hs, ?_⟩
      show some (s.gpr .r1 - BitVec.ofNat 32 x == 0) = some (decide (D = x))
      rw [h1 σ s hs, ofNat_sub_beq32 hD hx0]
    refine VP.ite (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun σ s hs => hs.1.1) fun _ _ h => h
      · exact VP.of_imp (p := False) (fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e) False.elim
    · by_cases hDx : D = x
      · exact VP.of_imp (p := False) (fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e) False.elim
      · exact (byLen_vp hD h1 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono (fun σ s hs => hs.1.1) fun _ _ h => h

end VG.Proof.RsaOaep.Arm
