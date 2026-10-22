module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
public import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# RSAES-OAEP on x86: the calls of the streaming hash functions

In the setting of the x86 RSASSA-PSS proofs (`Proof/RsaPss/X86/Base.lean`:
`Ctx L scr σ s`, a state of the body with our part of `scratch` at `scr` in
`ebp`), the streaming `init` (`init_vp`), `update` in its frame (`upd_vp`,
of any public range of bytes the body may read) and `finalize` in its frame
(`fin_vp`) of a hash function `G` (a `Pbkdf2.Stream.X86.HashOK`), on the
state at `scratch + oSt` with the working space at `scratch` itself: each
keeps any fact about memory (`Inv`) that its writes (the state, the working
space, the digest and the stack below the frame) do not reach, and is
constant time when its arguments are public.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oRsa frameBytes)
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK InitArgs UpdArgs FinArgs init_frame init_rel upd_frame upd_rel fin_frame
  fin_rel stk zero_append_ofNat)

variable {L : Lay} {scr : BitVec 32}

section
variable (hg : Geo L scr)
include hg

/-- A range of our part of `scratch` may be written, as one range. -/
theorem covS {σ s : State} (hs : L.St σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    Covers [⟨(scr + BitVec.ofNat 32 o).setWidth 64, n⟩] s.wr := by
  rw [hg.scrA ho]
  exact Covers.one (hg.wr hs h)

/-- The working space at `scratch` itself may be written. -/
theorem covW {σ s : State} (hs : L.St σ s) {n : Nat} (h : n ≤ oRsa) : Covers [⟨scr.setWidth 64, n⟩] s.wr := by
  rw [← sR0]
  exact Covers.one (hg.wr hs (o := 0) (by omega))

theorem fitS {o n : Nat} (h : o + n ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [hg.scr_lt (by omega)]; have := hg.fit; unfold oRsa at *; omega

theorem fitW {n : Nat} (h : n ≤ oRsa) : scr.toNat + n ≤ 2 ^ 32 := by
  have := hg.fit; unfold oRsa at *; omega

/-- The stack below the frame misses a range of our part of `scratch`. -/
theorem stkS {σ s : State} (hc : Ctx L scr σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    (stk s).Disjoint ⟨(scr + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  rw [hg.scrA ho]
  exact (hg.low hc.st.ok h).symm.sub_left (stk_low hg hc)

theorem stkW {σ s : State} (hc : Ctx L scr σ s) {n : Nat} (h : n ≤ oRsa) :
    (stk s).Disjoint ⟨scr.setWidth 64, n⟩ := by
  rw [← sR0]
  exact (hg.low hc.st.ok (o := 0) (by omega)).symm.sub_left (stk_low hg hc)

theorem sp48 {σ s : State} (hc : Ctx L scr σ s) : 48 ≤ (s.gpr .esp).toNat := by
  rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega

/-- A write to ranges of our part of `scratch` and of the stack below the
frame keeps `Ctx`. -/
theorem ctxW {σ s t : State} (hc : Ctx L scr σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, (∃ o n, o + n ≤ oRsa ∧ r = sR scr o n) ∨ r = L.LOW)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx L scr σ t :=
  hc.write hf (fun r hr => by
    rcases hs r hr with ⟨o, n, h, rfl⟩ | rfl
    · exact hg.inW h
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩) rd wr sp bp

end

/-- The bytes `[p, p + n)` the body may read, as one range. -/
theorem rbufCov {p : BitVec 32} {n : Nat} (hb : RBuf L p n) {σ s : State} (hs : L.St σ s) :
    Covers [⟨p.setWidth 64, n⟩] (s.rd ++ s.wr) := by
  obtain ⟨R, hR, hc⟩ := hb.r
  refine Covers.one ⟨R, ?_, hc⟩
  rw [hs.rd, hs.wr, hs.ok.rd, hs.ok.wr]
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _ hR
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hR)))

/-! ## `init` -/

theorem init_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem) (.seq (.block initArgs) (callInit G))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) []) := by
  have hS := hG.hSB
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt)
    (VP.taint [.esp, .ebp] initArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi⟩ => ?_) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => WP.block_nil ⟨(hc.upd u1 (by decide) (by decide)).upd u2
      (by decide) (by decide), by rw [u2.mem, u1.mem]; exact hi, by rw [u2.gpr, u1.gpr, hc.ebp]⟩
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSt →
      InitArgs (H := G) s .ebx (scr + BitVec.ofNat 32 oSt) := fun σ s hc bx =>
    ⟨bx, by decide, sp48 hg hc, covS hg hc.st (by oomega) (by oomega), stkS hg hc (by oomega) (by oomega),
      fitS hg (by oomega)⟩
  refine VP.of_ct (fun _ _ => init_rel hG (sp := L.B) fun a b hab =>
    ⟨args _ _ hab.1.1 hab.1.2.2, args _ _ hab.2.1 hab.2.2.2, hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, bx⟩
  refine init_frame hG (args σ s hc bx) fun s' af rp => ?_
  have aS : (scr + BitVec.ofNat 32 oSt).setWidth 64 = sa scr oSt := hg.scrA (by oomega)
  have fr : Frame [sR scr oSt G.S, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, stk_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), hI σ _ _ hi fr,
    by rw [← aS]; exact rp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
  · exact .inr rfl

/-! ## `update`, in its frame -/

/-- What `update`'s frame needs: the state (`ebx`), the data `[d, d + len)`
(in `edx`, `ecx`) and the count `c` (`edi`, `eax`); the working space is
`scratch` itself, in `ebp`. -/
structure UArgs (scr d : BitVec 32) (len c : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = scr + BitVec.ofNat 32 oSt
  edi : s.gpr .edi = BitVec.ofNat 32 c
  eax : s.gpr .eax = 0
  edx : s.gpr .edx = d
  ecx : s.gpr .ecx = BitVec.ofNat 32 len

theorem upd_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {d : BitVec 32} {len c : Nat}
    (hd : RBuf L d len) (dS : Region.Disjoint ⟨d.setWidth 64, len⟩ (sR scr oSt G.S))
    (dW : Region.Disjoint ⟨d.setWidth 64, len⟩ (sR scr oCW hG.Wb)) (dL : Region.Disjoint ⟨d.setWidth 64, len⟩ L.LOW)
    (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr oCW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg dat : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        Spec.Sha256.bytesAt s.mem (d.setWidth 64) len = dat σ ∧ UArgs scr d len c s)
      (callUpd G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ ++ dat σ)) := by
  have hS := hG.hSB
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : (scr + BitVec.ofNat 32 oSt).setWidth 64 = sa scr oSt := hg.scrA (by oomega)
  have eW : (⟨scr.setWidth 64, hG.Wb⟩ : Region) = sR scr oCW hG.Wb := (sR0 scr _).symm
  have ua : ∀ σ s, Ctx L scr σ s → UArgs scr d len c s →
      UpdArgs hG s .edi .ebx (scr + BitVec.ofNat 32 oSt) d scr (BitVec.ofNat 32 c) len := by
    intro σ s hc u
    refine ⟨u.ebx, u.edi, u.eax, u.ecx, u.edx, hc.ebp, by decide, by decide, hd.n32, sp48 hg hc, rbufCov hd hc.st,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (covW hg hc.st (by oomega)), ?_, by rw [aS]; exact dS,
      by rw [eW]; exact dW, stkS hg hc (by oomega) (by oomega), dL.symm.sub_left (stk_low hg hc), stkW hg hc (by oomega),
      fitS hg (by oomega), hd.fit, fitW hg (by oomega)⟩
    rw [aS, eW]; exact Geo.sep (by oomega) (by oomega) (by oomega)
  refine VP.of_ct (fun _ _ => upd_rel hG (sp := L.B) fun a b hab => ⟨ua _ _ hab.1.1 hab.1.2.2.2.2.2,
    ua _ _ hab.2.1 hab.2.2.2.2.2.2, hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, hdat, u⟩
  refine upd_frame hG (ua σ s hc u) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr oCW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [eW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), stk_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨oCW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [hl, zero_append_ofNat hc32])
  rw [aS, hdat] at this
  exact this

/-! ## `finalize`, in its frame -/

/-- What `finalize`'s frame needs: the state (`ebx`), the count `c` (`eax`,
`ecx`) and `out` at `scratch + o` (`edx`); the working space is `scratch`
itself, in `ebp`. -/
structure FArgs (scr : BitVec 32) (o c : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = scr + BitVec.ofNat 32 oSt
  eax : s.gpr .eax = BitVec.ofNat 32 c
  ecx : s.gpr .ecx = 0
  edx : s.gpr .edx = scr + BitVec.ofNat 32 o

theorem fin_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {o c : Nat} (ho1 : o + G.F ≤ oSt ∨ oSt + G.S ≤ o)
    (ho2 : oCW + hG.Wb ≤ o) (hoR : o + G.F ≤ oRsa) (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr o G.F, sR scr oCW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        FArgs scr o c s)
      (callFin G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        (Spec.Sha256.bytesAt s.mem (sa scr o) G.F).take G.D = hG.SH.H.hash (msg σ)) := by
  have hS := hG.hSB
  have hF := hG.hF
  have hF0 : 0 < G.F := by have := hG.hD0; have := hG.hDF; omega
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : (scr + BitVec.ofNat 32 oSt).setWidth 64 = sa scr oSt := hg.scrA (by oomega)
  have aO : (scr + BitVec.ofNat 32 o).setWidth 64 = sa scr o := hg.scrA (by oomega)
  have eW : (⟨scr.setWidth 64, hG.Wb⟩ : Region) = sR scr oCW hG.Wb := (sR0 scr _).symm
  have fa : ∀ σ s, Ctx L scr σ s → FArgs scr o c s →
      FinArgs hG s .ebx (scr + BitVec.ofNat 32 oSt) (scr + BitVec.ofNat 32 o) scr (BitVec.ofNat 32 c) 0 := by
    intro σ s hc f
    refine ⟨f.ebx, f.eax, f.ecx, f.edx, hc.ebp, by decide, sp48 hg hc,
      Covers.cons (covS hg hc.st (by oomega) (by oomega))
        (Covers.cons (covS hg hc.st (by oomega) hoR) (covW hg hc.st (by oomega))),
      ?_, ?_, ?_, stkS hg hc (by oomega) (by oomega), stkS hg hc (by oomega) hoR, stkW hg hc (by oomega),
      fitS hg (by oomega), fitS hg hoR, fitW hg (by oomega)⟩
    · rw [aS, aO]; exact Geo.sep (by omega) (by oomega) hoR
    · rw [aS, eW]; exact Geo.sep (by oomega) (by oomega) (by oomega)
    · rw [aO, eW]; exact Geo.sep (.inr ho2) hoR (by oomega)
  refine VP.of_ct (fun _ _ => fin_rel hG (sp := L.B) fun a b hab => ⟨fa _ _ hab.1.1 hab.1.2.2.2.2,
    fa _ _ hab.2.1 hab.2.2.2.2.2, hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, f⟩
  refine fin_frame hG (fa σ s hc f) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr o G.F, sR scr oCW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [aO]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by rw [eW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        stk_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨o, G.F, hoR, rfl⟩
    · exact .inl ⟨oCW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [hl]; omega) (by rw [hl, zero_append_ofNat hc32])
  rw [aO] at this
  exact this

end VG.Proof.RsaOaep.X86
