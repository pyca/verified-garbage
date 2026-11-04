module

import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf

/-!
# RSAES-OAEP on x86: the label's hash with a table

`labelT_vp`: as `label_vp` (`Label.lean`), with the hash function that of
the table at `p`, whose address is in the slot `sTab`: each of its calls
through the table (`tcallG_vp`, as `tcallK_vp` for MGF1) runs as the
function's own, in every run at the same address (`TabFacts`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oDig oEm oRsa frameBytes arg)
open VG.Impl.RsaOaep.X86 (Fns tcall sTab)

variable {L : Lay} {scr : BitVec 32}

/-- The call of the table's function `k`, among `ts`, in a frame pushing
`rs`, from a stage with `Ctx`, what the caller keeps (`Inv`: the table's
address in its slot, and what the table holds in every run) and `X`, which
an update of `esi` keeps: as the call of `n`, at `a` in every run. -/
theorem tcallG_vp (hg : Geo L scr) {g : OHash} {f : Fns} {p ai au af : BitVec 32}
    (tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (VG.X86.addr p o) 4) {Inv : State → Mem → Prop}
    (hS : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p) (hT : ∀ σ m, Inv σ m → TabFacts g.H f p ai au af σ)
    {X : State → State → Prop} (hX : ∀ σ s t v, X σ s → Upd s t .esi v → X σ t) {k : Nat}
    (hk3 : k < 3) {ts : List (String × Prog isa)} {rs : List Reg} {n : String} {cn : Prog isa}
    {a : BitVec 32} (hne : ts ≠ [])
    (ha : ∀ σ, TabFacts g.H f p ai au af σ →
      σ.mem.readW (VG.X86.addr p (4 * k)) 32 = a ∧ σ.syms n = a ∧
        ts.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms n).setWidth 64) = some (n, cn))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms)
      (.frame (.push rs) (.call n cn) (.pop .eax rs.length)) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms) (tcall k ts rs) G := by
  have hk : 4 * k + 4 ≤ 20 := by omega
  obtain ⟨tR, tRo, tC⟩ := tbl
  let F : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms
  have keepF : ∀ σ s t v, F σ s → Upd s t .esi v → F σ t := fun σ s t v ⟨⟨hc, hm, hx⟩, sy⟩ u =>
    ⟨⟨hc.upd u (by decide) (by decide), u.mem ▸ hm, hX σ s t v hx u⟩, u.syms.trans sy⟩
  refine tcall_vp (F₁ := fun σ s => F σ s ∧ s.gpr .esi = a) hne ?_ ?_ ?_
    (h.mono (fun σ s hs => hs.1) fun _ _ h => h)
  · show VP F (.block ([Impl.RsaPss.X86.ld .esi sTab] ++ [.mov .esi (.mem (Impl.RsaPkcs1Sig.X86.at_ .esi (4 * k)))]))
      (fun σ s => F σ s ∧ s.gpr .esi = a)
    refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .esi = p)
      (VP.taint [.esp, .ebp] tload_taint (sp_bp fun _ _ h => h.1.1) fun σ s hs => ?_)
      (VP.taint [.esp, .ebp, .esi] (tword_taint hk3) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    · simp only [Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.stk]
      refine hs.1.1.wp_slot hg (by decide) (by decide) (by decide) fun t1 _ u1 => WP.block_nil ⟨keepF σ s t1 _ hs u1, ?_⟩
      rw [u1.gpr, hS σ _ hs.1.2.1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]
      · rw [h₁.1.1.1.ebp, h₂.1.1.1.ebp]
      · rw [h₁.2, h₂.2]
    · obtain ⟨hF, hsi⟩ := hs
      have T := hT σ _ hF.1.2.1
      have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr p (4 * k)) 4 :=
        ⟨tR, hF.1.1.st.inRo tRo, tC _ hk⟩
      refine wp_ldm (B := p) hsi hin fun t2 u2 => WP.block_nil ⟨keepF σ s t2 _ hF u2, ?_⟩
      rw [u2.gpr, St_roW hF.1.1.st tRo (tC _ hk), (ha σ T).1]
  · intro σ s ⟨hF, hsi⟩
    have T := hT σ _ hF.1.2.1
    obtain ⟨-, hn, hf⟩ := ha σ T
    show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .esi).setWidth 64) = some (n, cn)
    rw [hsi, hF.2, ← hn]
    exact hf
  · intro σ₁ σ₂ s₁ s₂ h₁ h₂
    exact ⟨h₁.2.trans h₂.2.symm, h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm⟩

/-- The label's hash, with the hash function `h` of the table at `p`. -/
theorem labelT_vp (hg : Geo L scr) (h : OHash) {f : Fns} {p ai au af : BitVec 32}
    (tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (VG.X86.addr p o) 4)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) {j o ll : Nat} {lab : BitVec 32} (hj : j + 1 < L.argv.length)
    (ht : TaintOk [.esp, .ebp] (.block (updLabArgs j))) (ht' : TaintOk [.esp, .ebp] (.block (finLabArgs j o)))
    (hlab : L.argv.getD j 0 = lab) (hll : L.argv.getD (j + 1) 0 = BitVec.ofNat 32 ll)
    (hb : RBuf L lab ll) (dS : Region.Disjoint ⟨lab.setWidth 64, ll⟩ (sR scr oSt h.H.S))
    (dW : Region.Disjoint ⟨lab.setWidth 64, ll⟩ (sR scr oCW h.ok.Wb))
    (dL : Region.Disjoint ⟨lab.setWidth 64, ll⟩ L.LOW)
    (ho1 : oSt + 256 ≤ o) (ho2 : o + 64 ≤ oEm) {labB : State → List Byte}
    (hbytes : ∀ σ s, Ctx L scr σ s → Spec.Sha256.bytesAt s.mem (lab.setWidth 64) ll = labB σ)
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' → Inv σ m')
    (hS : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p) (hT : ∀ σ m, Inv σ m → TabFacts h.H f p ai au af σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem) ∧ s.syms = σ.syms)
      (hashLabelT f j o)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.H.D, s.mem (sa scr (o + i)) = (h.G.hash (labB σ)).getD i 0) ∧ s.syms = σ.syms) := by
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.DF
  have hll32 : ll < 2 ^ 32 := hb.n32
  have ofr : ∀ m m', Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW] m m' →
      Frame [sR scr oSt h.H.S, sR scr oCW h.ok.Wb, L.LOW, sR scr o h.H.F] m m' :=
    fun _ _ f => f.mono (by simp)
  show VP _ (.seq (.block initArgs) (.seq (callInit f) (.seq (.block (updLabArgs j)) (.seq (callUpd f)
    (.seq (.block (finLabArgs j o)) (callFin f)))))) _
  -- `init`.
  refine VP.seq (VP.syms initArgs_vp) (VP.seq (tcallG_vp hg tbl hS hT
    (X := fun _ s => s.gpr .ebx = scr + BitVec.ofNat 32 oSt)
    (fun _ _ _ _ h u => (u.other .ebx (by decide)).trans h) (k := 0) (by decide) fne.1 (a := ai)
    (fun σ T => ⟨T.mem.1.trans T.ai, T.ai, T.ok.i⟩)
    ((VP.syms (initCall_vp hg h.H h.ok (Inv := Inv) fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp)))).mono
      (fun σ s ⟨⟨hc, hm, hb⟩, sy⟩ => ⟨⟨hc, hm, hb⟩, sy⟩) fun _ _ h => h)) ?_)
  -- `update`'s arguments.
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (lab.setWidth 64) ll = labB σ ∧
      UArgs scr lab ll 0 s) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] ht (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, rp⟩ => ?_)) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => ?_
    have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
      (by decide) (by decide)).upd u4 (by decide) (by decide)
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine c4.wp_arg hg (by omega) (by decide) (by decide) fun t5 c5 u5 =>
      c5.wp_arg hg hj (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, m4]
    refine ⟨c6, m6 ▸ hi, m6 ▸ rp, rfl, hbytes σ t6 c6, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · rw [u6.other _ (by decide), u5.gpr, hlab]
    · rw [u6.gpr, hll]
  -- `update` with the label.
  refine VP.seq (tcallG_vp hg tbl hS hT (X := fun σ s => h.ok.SH.Repr s.mem (sa scr oSt) [] ∧
      ([] : List Byte).length = 0 ∧ Spec.Sha256.bytesAt s.mem (lab.setWidth 64) ll = labB σ ∧ UArgs scr lab ll 0 s)
    (fun _ _ _ _ ⟨r, l, b, ua⟩ u => ⟨u.mem ▸ r, l, u.mem ▸ b, ua.esi u⟩) (k := 1) (by decide) fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩)
    (VP.syms (upd_vp hg h.H h.ok (msg := fun _ => []) (dat := labB) (c := 0) (Inv := Inv) hb dS dW dL (by decide)
      fun σ m m' hm hf => hI σ m m' hm (ofr _ _ hf)))) ?_
  -- `finalize`'s arguments.
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] ht' (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, rp⟩ => ?_)) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg hj (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => ?_
    refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => WP.block_nil ?_
    have c6 : Ctx L scr σ t6 := (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
      (by decide) (by decide))
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨c6, m6 ▸ hi, m6 ▸ rp, by rw [List.nil_append, ← hbytes σ s hc, Spec.Sha256.bytesAt, List.length_map,
      List.length_range], ⟨?_, ?_, ?_, ?_⟩⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hll]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · simp (disch := decide) only [u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
  -- `finalize`.
  have hfin := tcallG_vp hg tbl hS hT (X := fun σ s => h.ok.SH.Repr s.mem (sa scr oSt) ([] ++ labB σ) ∧
      ([] ++ labB σ).length = ll ∧ FArgs scr o ll s)
    (fun _ _ _ _ ⟨r, l, fa⟩ u => ⟨u.mem ▸ r, l, fa.esi u⟩) (k := 2) (by decide) fne.2.2 (a := af)
    (fun σ T => ⟨T.mem.2.2.trans T.af, T.af, T.ok.f⟩)
    (VP.syms (fin_vp hg h.H h.ok (o := o) (c := ll) (msg := fun σ => [] ++ labB σ) (Inv := Inv) (.inr (by omega))
      (by oomega) (by oomega) hll32 fun σ m m' hm hf => hI σ m m' hm (hf.mono (by simp))))
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

/-- `byLen` from stages with the digest length `D` in `edx`, which a `cmp`
keeps: the branch of `D`. -/
theorem byLen_vp {F G : State → State → Prop} {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 32)
    (h16 : ∀ σ s, F σ s → s.gpr .edx = BitVec.ofNat 32 D)
    (hst : ∀ σ s t, F σ s → Fupd s t → t.syms = s.syms → F σ t)
    (hb : VP F (b D) G) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 2 ^ 32 ∧
      TaintOk [] (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 x))])) → VP F (byLen b ds) G
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, htx⟩ := hx x (List.mem_cons_self ..)
    refine VP.seq (G := fun σ s => F σ s ∧ isa.eval .e s = some (decide (D = x)))
      (VP.taint [] htx (fun _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) fun σ s hs =>
        WP.mono_syms (Q := fun t => Fupd s t ∧ t.zf = some (s.gpr .edx - BitVec.ofNat 32 x == 0))
          (wp_cmpi fun t f _ z => WP.block_nil ⟨f, z⟩) fun t ⟨f, z⟩ sy => ⟨hst σ s t hs f sy, ?_⟩) ?_
    · show eval .e t = _
      simp only [eval, z, h16 σ s hs, ofNat_sub_beq32 hD hx0]
    refine VP.ite (fun σ s hs => ⟨_, hs.2⟩) (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun σ s hs => hs.1.1) fun _ _ h => h
      · exact VP.empty fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e
    · by_cases hDx : D = x
      · exact VP.empty fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e
      · exact (byLen_vp hD h16 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono (fun σ s hs => hs.1.1) fun _ _ h => h

end VG.Proof.RsaOaep.X86
