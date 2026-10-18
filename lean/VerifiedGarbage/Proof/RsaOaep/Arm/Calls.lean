module

public import VerifiedGarbage.Impl.RsaOaep.Arm
public import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
public import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm

/-!
# RSAES-OAEP on ARMv7: the calls of the streaming hash functions

In the setting of the ARMv7 RSASSA-PSS proofs (`Proof/RsaPss/Arm/Base.lean`:
`Ctx L scr σ s`, a state of the body with our part of `scratch` at `scr`),
the streaming `init` (`init_vp`), `update` in its frame (`upd_vp`, of any
public range of bytes the body may read) and `finalize` in its frame
(`fin_vp`) of a hash function `G` (a `Pbkdf2.Stream.Arm.HashOK`), on the
state at `scratch + oSt` with the working space at `scratch + oW`: each
keeps any fact about memory (`Inv`) that its writes (the state, the
working space, the digest and the stack below the frame) do not reach, and
is constant time when its arguments are public.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa)
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK count)
open VG.Proof.Rsa.Arm.Recover (VP)

theorem sSrc_lt : sSrc < 4096 := by decide
theorem sSrcLen_lt : sSrcLen < 4096 := by decide
theorem sDst_lt : sDst < 4096 := by decide
theorem sDstLen_lt : sDstLen < 4096 := by decide
theorem sRes_lt : sRes < 4096 := by decide
theorem sOk_lt : sOk < 4096 := by decide

theorem offsO : oEm = 0 ∧ oBuf = 1024 ∧ oSt = 3072 ∧ oDig = 3328 ∧ oLh = 3392 ∧ oCtr = 3456 ∧ oW = 3520 ∧
    oRsa = 8192 ∧ frameBytes = 128 ∧ sS = 64 ∧ sSrc = 68 ∧ sSrcLen = 72 ∧ sDst = 76 ∧ sDstLen = 80 ∧ sRes = 84 ∧
    sOk = 88 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers. -/
macro "oomega" : tactic => `(tactic| (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := offsO; omega))

variable {L : Lay} {scr : BitVec 32}

/-- The bytes `[d, d + n)` the body may read, as one range. -/
theorem rbufCov {p : BitVec 32} {n : Nat} (hb : RBuf L p n) {σ s : State} (hs : L.St σ s) :
    Covers [⟨State.addr p, n⟩] (s.rd ++ s.wr) := by
  obtain ⟨R, hR, hc⟩ := hb.r
  refine Covers.one ⟨R, ?_, hc⟩
  rw [hs.rd, hs.wr, hs.ok.rd, hs.ok.wr]
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _ (List.mem_append_left _ hR)
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR))

section
variable (hg : Geo L scr)
include hg

/-- A range of our part of `scratch` may be written, as one range. -/
theorem covS {σ s : State} (hs : L.St σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    Covers [⟨State.addr (scr + BitVec.ofNat 32 o), n⟩] s.wr := by
  rw [hg.addr ho]
  exact Covers.one (hg.wr hs h)

theorem fitS {o n : Nat} (h : o + n ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [hg.scr_lt (by omega)]; have := hg.fit; unfold oRsa at *; omega

/-- The stack below the frame and a range of our part of `scratch`. -/
theorem belowS {σ s : State} (hc : Ctx L scr σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    (Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr (scr + BitVec.ofNat 32 o), n⟩ := by
  obtain ⟨σ', ok⟩ := hg.ok
  rw [hg.addr ho]
  exact (hg.low ok h).symm.sub_left (below_low hg hc)

theorem sp16 {σ s : State} (hc : Ctx L scr σ s) : 16 ≤ s.sp.toNat := by
  rw [hc.st.sp]; have := hg.C16; have := hc.st.ok.B56; omega

/-- A write to a range of our part of `scratch` and the stack below the
frame keeps `Ctx`. -/
theorem ctxW {σ s t : State} (hc : Ctx L scr σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, (∃ o n, o + n ≤ oRsa ∧ r = sR scr o n) ∨ r = L.LOW)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : Ctx L scr σ t := by
  obtain ⟨σ', ok⟩ := hg.ok
  refine hc.write hf (fun r hr => ?_) (fun r hr => ?_) rd wr sp
  · rcases hs r hr with ⟨o, n, h, rfl⟩ | rfl
    · exact hg.inW h
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · rcases hs r hr with ⟨o, n, h, rfl⟩ | rfl
    · exact hg.slot ok h (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega)

end

/-! ## `init` -/

theorem init_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem)
      (.seq (.block initArgs) (.call G.initN G.initC))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) []) := by
  have hS := hG.hSB
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
    (VP.blk (by decide) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi⟩ => ?_) ?_
  · prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
      movw_val (show oSt < 2 ^ 16 by decide)]
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + G.S ≤ 2 ^ 32 := fitS hg (by oomega)
  have cov : ∀ σ s, Ctx L scr σ s → Covers [⟨State.addr (scr + BitVec.ofNat 32 oSt), G.S⟩] s.wr :=
    fun σ s hc => covS hg hc.st (by oomega) (by oomega)
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.init_rel hG (st := scr + BitVec.ofNat 32 oSt)
    fun a b hab => ⟨hab.1.2.2, hab.2.2.2, fitS, cov _ _ hab.1.1, cov _ _ hab.2.1⟩) ?_
  rintro σ s ⟨hc, hi, r0⟩
  refine Pbkdf2.Stream.Arm.init_call hG r0 fitS (cov _ _ hc) fun s' af rp => ?_
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have fr : Frame [sR scr oSt G.S, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, by rw [← aS]; exact rp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
  · exact .inr rfl

/-! ## `update`, in its frame -/

/-- What `update`'s frame needs: the state, the data `[d, d + len)` (in
`r1`, `r7`), the working space (`r10`) and the count `c` (`r2:r3`). -/
structure UArgs (scr d : BitVec 32) (len c : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 oSt
  r1 : s.gpr .r1 = d
  r7 : s.gpr .r7 = BitVec.ofNat 32 len
  r10 : s.gpr .r10 = scr + BitVec.ofNat 32 oW
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  r3 : s.gpr .r3 = 0

theorem count_of {s : State} {c : Nat} (hc : c < 2 ^ 32) (h2 : s.gpr .r2 = BitVec.ofNat 32 c) (h3 : s.gpr .r3 = 0) :
    count s = BitVec.ofNat 64 c := by
  simp only [count, h2, h3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega)]
  simp

theorem upd_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {d : BitVec 32} {len c : Nat}
    (hd : RBuf L d len) (dS : Region.Disjoint ⟨State.addr d, len⟩ (sR scr oSt G.S))
    (dW : Region.Disjoint ⟨State.addr d, len⟩ (sR scr oW hG.Wb)) (dL : Region.Disjoint ⟨State.addr d, len⟩ L.LOW)
    (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr oW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg dat : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        Spec.Sha256.bytesAt s.mem (State.addr d) len = dat σ ∧ UArgs scr d len c s)
      (updCall G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ ++ dat σ)) := by
  have hS := hG.hSB
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have aW : State.addr (scr + BitVec.ofNat 32 oW) = sa scr oW := hg.addr (by oomega)
  have sw : Region.Disjoint (sR scr oSt G.S) (sR scr oW hG.Wb) := Geo.sep (by oomega) (by oomega) (by oomega)
  have ua : ∀ σ s, Ctx L scr σ s → UArgs scr d len c s →
      Pbkdf2.Whole.Arm.UpdL hG s (scr + BitVec.ofNat 32 oSt) d (scr + BitVec.ofNat 32 oW) len := by
    intro σ s hc u
    refine ⟨u.r0, u.r1, u.r7, u.r10, hd.n32, sp16 hg hc, rbufCov hd hc.st,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (covS hg hc.st (by oomega) (by oomega)), by rw [aS, aW]; exact sw,
      by rw [aS]; exact dS, by rw [aW]; exact dW, belowS hg hc (by oomega) (by oomega), dL.symm.sub_left (below_low hg hc),
      belowS hg hc (by oomega) (by oomega), fitS hg (by oomega), hd.fit, fitS hg (by oomega)⟩
  refine VP.of_ct (fun _ _ => Pbkdf2.Whole.Arm.upd_rel hG (sp := L.B) fun a b hab => ⟨ua _ _ hab.1.1 hab.1.2.2.2.2.2,
    ua _ _ hab.2.1 hab.2.2.2.2.2.2, by rw [count_of hc32 hab.1.2.2.2.2.2.r2 hab.1.2.2.2.2.2.r3,
      count_of hc32 hab.2.2.2.2.2.2.r2 hab.2.2.2.2.2.2.r3], hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, hdat, u⟩
  refine Pbkdf2.Whole.Arm.upd_frame hG (ua σ s hc u) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr oW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [aW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨oW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [count_of hc32 u.r2 u.r3, hl])
  rw [aS, hdat] at this
  exact this

/-! ## `finalize`, in its frame -/

/-- What `finalize`'s frame needs: the state, `out` at `scratch + o` (`r1`),
the working space (`r12`) and the count `c` (`r2:r3`). -/
structure FArgs (scr : BitVec 32) (o c : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 oSt
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 o
  r12 : s.gpr .r12 = scr + BitVec.ofNat 32 oW
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  r3 : s.gpr .r3 = 0

theorem fin_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {o c : Nat} (ho1 : o + G.F ≤ oSt ∨ oSt + G.S ≤ o)
    (ho2 : o + G.F ≤ oW ∨ oW + hG.Wb ≤ o) (hoR : o + G.F ≤ oRsa) (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr o G.F, sR scr oW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        FArgs scr o c s)
      (finCall G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (Spec.Sha256.bytesAt s.mem (sa scr o) G.F).take G.D = hG.SH.H.hash (msg σ)) := by
  have hS := hG.hSB
  have hF := hG.hF
  have hF0 : 0 < G.F := by have := hG.hD0; have := hG.hDF; omega
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have aW : State.addr (scr + BitVec.ofNat 32 oW) = sa scr oW := hg.addr (by oomega)
  have aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by oomega)
  have fa : ∀ σ s, Ctx L scr σ s → FArgs scr o c s →
      Pbkdf2.Stream.Arm.FinArgs hG s (scr + BitVec.ofNat 32 oSt) (scr + BitVec.ofNat 32 o)
        (scr + BitVec.ofNat 32 oW) := by
    intro σ s hc f
    refine ⟨f.r0, f.r1, f.r12, sp16 hg hc,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (Covers.cons (covS hg hc.st (by oomega) hoR) (covS hg hc.st (by oomega) (by oomega))),
      by rw [aS, aO]; exact Geo.sep (by omega) (by oomega) hoR, by rw [aS, aW]; exact Geo.sep (by oomega) (by oomega) (by oomega),
      by rw [aO, aW]; exact Geo.sep ho2 hoR (by oomega),
      belowS hg hc (by oomega) (by oomega), belowS hg hc (by oomega) hoR, belowS hg hc (by oomega) (by oomega), fitS hg (by oomega), fitS hg hoR,
      fitS hg (by oomega)⟩
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.fin_rel hG (sp := L.B) fun a b hab => ⟨fa _ _ hab.1.1 hab.1.2.2.2.2,
    fa _ _ hab.2.1 hab.2.2.2.2.2, by rw [count_of hc32 hab.1.2.2.2.2.r2 hab.1.2.2.2.2.r3,
      count_of hc32 hab.2.2.2.2.2.r2 hab.2.2.2.2.2.r3], hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, f⟩
  refine Pbkdf2.Stream.Arm.fin_frame hG (fa σ s hc f) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr o G.F, sR scr oW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [aO]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by rw [aW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨o, G.F, hoR, rfl⟩
    · exact .inl ⟨oW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [hl]; omega) (by rw [count_of hc32 f.r2 f.r3, hl])
  rw [aO] at this
  exact this

/-! ## `r12 := r10` -/

theorem toR12_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r10]) (.block toR12) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem toR12_vp {F : State → State → Prop} (hF : ∀ σ s, F σ s → s.gpr .r10 = scr + BitVec.ofNat 32 oW)
    (hX : ∀ σ s v, F σ s → F σ (s.setReg .r12 v)) :
    VP F (.block toR12) (fun σ s => F σ s ∧ s.gpr .r12 = scr + BitVec.ofNat 32 oW) := by
  refine VP.taint _ toR12_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [hF _ _ h₁, hF _ _ h₂]
  · apply WP.of_runBlock
    simp only [toR12, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    exact ⟨_, rfl, hX σ s _ hs, by rw [RegUpd.gpr_setReg]; simp [hF σ s hs]⟩

/-- An OR of two words is zero when both are. -/
theorem or_eq_zero32 (a b : BitVec 32) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro e
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun x => x.getLsbD i) e <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

end VG.Proof.RsaOaep.Arm
