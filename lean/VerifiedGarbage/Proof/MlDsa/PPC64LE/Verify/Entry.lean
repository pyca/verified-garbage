module
-- separate module: its proofs, generic over the kernel, build in parallel with those of the primitives, which `Inst` also imports

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Top
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# ML-DSA verification on PPC64LE: the entries

`entry n code p prepared` (`Impl/MlDsa/PPC64LE/Verify/Verify.lean`) calls
the kernel `code`, `vg_mldsa*_verify_with_cache` (`verifyWithCacheContract`),
with the cache at `pk + off` of `len` bytes: none (`vg_mldsa*_verify`,
against `verifyContract`, `verify_entry_verified`), or the polynomials a
prepared public key holds after its encoded key (`vg_mldsa*_verify_prepared`,
against `preparedVerifyContract`, `prepared_entry_verified`). Both contracts
have the key at `r3` in a region of `L` bytes and are otherwise the same
(`EPre`); the kernel's precondition holds of its entry state (`cs_kpre`),
the bytes of the inputs are those our caller gave (the entry's frame is on
the stack), and the result is the kernel's (`entryV_wp`). Two runs leak the
same if their entry states agree on what the contract makes public
(`entryV_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE (eSt eSt_gpr eSt_mem MvOk entryCode entry_wp entry_tr)
open VG.Proof.MlDsa.PPC64LE.KeyGen (scrLen reg)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The preconditions of the entries, with the key in `L` bytes and `X`. -/
structure EPre (p : Params) (L K : Nat) (X : State → Prop) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (vPk σ) L, reg (vMu σ) 64, reg (vSg σ) p.sigLen]
  wr : σ.wr = [reg (vScr σ) (scrLen p)]
  d_pc : (reg (vPk σ) L).Disjoint (reg (vScr σ) (scrLen p))
  d_mc : (reg (vMu σ) 64).Disjoint (reg (vScr σ) (scrLen p))
  d_sc : (reg (vSg σ) p.sigLen).Disjoint (reg (vScr σ) (scrLen p))
  b_p : (below σ.sp K).Disjoint (reg (vPk σ) L)
  b_m : (below σ.sp K).Disjoint (reg (vMu σ) 64)
  b_s : (below σ.sp K).Disjoint (reg (vSg σ) p.sigLen)
  b_c : (below σ.sp K).Disjoint (reg (vScr σ) (scrLen p))
  f_p : (vPk σ).toNat + L ≤ 2 ^ 64
  f_m : (vMu σ).toNat + 64 ≤ 2 ^ 64
  f_s : (vSg σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (vScr σ).toNat + scrLen p ≤ 2 ^ 64
  x : X σ

theorem epre_verify {p : Params} {k : Nat} {σ : State} (h : (verifyContract p PPC64LE.abi (k + 1)).pre σ) :
    EPre p p.pkLen (k + 1) (fun _ => True) σ := by
  sig_pre [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, trivial⟩

theorem epre_prepared {p : Params} {k : Nat} {σ : State}
    (h : (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (k + 1)).pre σ) :
    EPre p (preparedPublicKeyBytes p) (k + 1) (fun σ => PreparedPublicKey p σ.mem (vPk σ)) σ := by
  sig_pre [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem kpre_to {p : Params} {k : Nat} {σ : State} (h : KPre p (k + 1) σ) :
    (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (k + 1)).pre σ := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs]
  exact ⟨h.stk, h.rd, h.wr, h.d_pc, h.d_mc, h.d_sc, h.d_cx, h.b_p, h.b_m, h.b_s, h.b_c, h.b_x, h.f_p, h.f_m, h.f_s,
    h.f_c, h.f_x, h.polys⟩

/-! ## The call -/

/-- The moves of an entry: `r7 ← r3 + off`, `r8 ← len`. -/
abbrev eMv (off len : Nat) : List Instr := [.addi .r7 .r3 off, .li .r8 len]

/-- The state after them. -/
def eF (off len : Nat) (u : State) : State :=
  (u.write .r7 (u.gpr .r3 + BitVec.ofNat 64 off)).write .r8 (BitVec.ofNat 64 len)

theorem eMv_ok {off len : Nat} (ho : off < 2 ^ 15) (hl : len < 2 ^ 15) (u : State) :
    WP isa (.block (eMv off len)) u (· = eF off len u) :=
  WP.cons (exec_addi (by decide) ho) (WP.cons (exec_li hl) (WP.block_nil rfl))

theorem eF_ok (off len : Nat) : MvOk (eF off len) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u r hr => by
    have h7 : r ≠ .r7 := fun e => by subst e; simp [preserved] at hr
    have h8 : r ≠ .r8 := fun e => by subst e; simp [preserved] at hr
    simp only [eF, RegUpd.gpr_write_of_ne _ _ h7, RegUpd.gpr_write_of_ne _ _ h8]⟩

section
variable (p : Params) (off len : Nat)

/-- The regions the kernel is given. -/
abbrev rdC (σ : State) : List Region :=
  [reg (vPk σ) p.pkLen, reg (vMu σ) 64, reg (vSg σ) p.sigLen, reg (vPk σ + BitVec.ofNat 64 off) len]
abbrev wrC (σ : State) : List Region := [reg (vScr σ) (scrLen p)]

/-- The state the kernel starts in. -/
abbrev cs (σ : State) : State := (eF off len (eSt σ)).callEntry.withRegions (rdC p off len σ) (wrC p σ)

end

section
variable {p : Params} {off len : Nat}

theorem cs_gpr (σ : State) {r : Reg} (h0 : r ≠ .r0) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h11 : r ≠ .r11)
    (h12 : r ≠ .r12) : (cs p off len σ).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by simp [linkRegs, h0, h11, h12]), eF,
    RegUpd.gpr_write_of_ne _ _ h8, RegUpd.gpr_write_of_ne _ _ h7, eSt_gpr _ h0]

theorem cs_r7 (σ : State) : (cs p off len σ).gpr .r7 = σ.gpr .r3 + BitVec.ofNat 64 off := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), eF, RegUpd.gpr_write_of_ne _ _ (by decide),
    RegUpd.gpr_write_self, eSt_gpr _ (by decide)]

theorem cs_r8 (σ : State) : (cs p off len σ).gpr .r8 = BitVec.ofNat 64 len := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), eF, RegUpd.gpr_write_self]

theorem cs_sp (σ : State) : (cs p off len σ).sp = σ.sp - 48 := rfl

theorem cs_mem (σ : State) : Frame [below σ.sp 48] σ.mem (cs p off len σ).mem := eSt_mem σ

end

section
variable {p : Params} {L K off len : Nat} {X : State → Prop} {σ : State}
  (h : EPre p L (K + 1 + 48) X σ) (hL : p.pkLen ≤ L) (hoff : off + len ≤ L) (hlen : len < 2 ^ 64)
  (hO : off < 2 ^ 64)
  (hc : len = 0 ∨ (len = 4 * n * p.k ∧
    Proof.MlDsa.CachedPublicPolys p σ.mem (vPk σ + BitVec.ofNat 64 off) (pkOf p σ)))
include h

theorem EPre.fit : K + 1 + 48 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega

theorem EPre.b48 : Region.Sub (below σ.sp 48) (below σ.sp (K + 1 + 48)) := below_sub (by omega) h.fit

theorem EPre.bK : Region.Sub (below (σ.sp - 48) (K + 1)) (below σ.sp (K + 1 + 48)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have := h.fit; have := h.stk
  bv_omega

/-- Bytes apart from the stack are as on entry, for the kernel. -/
theorem EPre.bytes {a : Addr} {l : Nat} (hd : (below σ.sp (K + 1 + 48)).Disjoint (reg a l)) (hl : l ≤ 2 ^ 64) :
    bytesAt (cs p off len σ).mem a l = bytesAt σ.mem a l :=
  Proof.MlKem.bytesAt_frame (cs_mem σ) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left h.b48).symm) hl

omit h in
include hL in
theorem EPre.subK : Region.Sub (reg (vPk σ) p.pkLen) (reg (vPk σ) L) := by
  have := Offset.sub_base (vPk σ) (d := 0) (n := p.pkLen) (k := L) (by omega)
  rwa [BitVec.add_zero] at this

omit h in
include hoff in
theorem EPre.subX : Region.Sub (reg (vPk σ + BitVec.ofNat 64 off) len) (reg (vPk σ) L) := Offset.sub_base _ hoff

include hL in
theorem EPre.inputs : pkOf p (cs p off len σ) = pkOf p σ ∧ muOf (cs p off len σ) = muOf σ ∧
    sgOf p (cs p off len σ) = sgOf p σ := by
  simp only [pkOf, muOf, sgOf, vPk, vMu, vSg, cs_gpr σ (r := .r3) (by decide) (by decide) (by decide) (by decide)
    (by decide), cs_gpr σ (r := .r4) (by decide) (by decide) (by decide) (by decide) (by decide),
    cs_gpr σ (r := .r5) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ⟨h.bytes (h.b_p.sub_right (EPre.subK hL)) (by have := h.f_p; simp only [vPk] at this; omega),
    h.bytes h.b_m (by decide),
    h.bytes h.b_s (by have := h.f_s; simp only [vSg] at this; omega)⟩

include hL hoff hlen hc hO in
/-- The kernel's precondition holds of the state it starts in. -/
theorem cs_kpre : KPre p (K + 1) (cs p off len σ) := by
  have e3 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r3) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e4 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r4) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e5 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r5) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e6 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e8 : ((cs p off len σ).gpr .r8).toNat = len := by
    rw [cs_r8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  have sK : Region.Sub (reg (vPk σ) p.pkLen) (reg (vPk σ) L) := EPre.subK hL
  have sX : Region.Sub (reg (vPk σ + BitVec.ofNat 64 off) len) (reg (vPk σ) L) := EPre.subX hoff
  have fk := h.f_p
  simp only [vPk] at fk
  have bK := h.bK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [vPk, vMu, vSg, vScr, e3, e4, e5, e6, e8, cs_r7, cs_sp] at *
  · have := h.stk; have := h.fit; bv_omega
  · rfl
  · rfl
  · exact h.d_pc.sub_left sK
  · exact h.d_mc
  · exact h.d_sc
  · exact (h.d_pc.sub_left sX).symm
  · exact (h.b_p.sub_left bK).sub_right sK
  · exact h.b_m.sub_left bK
  · exact h.b_s.sub_left bK
  · exact h.b_c.sub_left bK
  · exact (h.b_p.sub_left bK).sub_right sX
  · omega
  · exact h.f_m
  · exact h.f_s
  · exact h.f_c
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hO]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)
  · rw [cs_r8]
    rcases hc with h0 | ⟨hl, hcc⟩
    · subst h0; exact .inl rfl
    · refine .inr ⟨hl, fun i hi => ?_⟩
      rw [(h.inputs hL).1]
      have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r3 + BitVec.ofNat 64 off +
          BitVec.ofNat 64 (4 * n * i))) (reg (σ.gpr .r3 + BitVec.ofNat 64 off) len) :=
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * p.k; omega)
      exact Proof.MlDsa.Verify.polyIs_frame (cs_mem σ) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ((h.b_p.sub_left h.b48).sub_right sX).symm.sub_left hsub) (hcc i hi)

end

/-! ## The entries -/

section
variable {p : Params} {L K off len : Nat} {X : State → Prop} {name : String} {code : Prog isa}
  (hv : Verified PPC64LE.target code (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (K + 1)))
  (hd : sdepth code ≤ K + 1) (hK : K + 1 + 48 < 2 ^ 64) (hL : p.pkLen ≤ L) (hoff : off + len ≤ L)
  (ho : off < 2 ^ 15) (hl : len < 2 ^ 15)
  (hc : ∀ σ, EPre p L (K + 1 + 48) X σ → len = 0 ∨ (len = 4 * n * p.k ∧
    Proof.MlDsa.CachedPublicPolys p σ.mem (vPk σ + BitVec.ofNat 64 off) (pkOf p σ)))
include hv hd hK hL hoff ho hl hc

omit hv hd hK hL hoff ho hl hc in
theorem EPre.hd96 {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    ∀ R ∈ σ.wr, Region.Disjoint ⟨σ.sp - 48 + 32, 16⟩ R := fun R hR => by
  have hs : Region.Sub ⟨σ.sp - 48 + 32, 16⟩ (below σ.sp (K + 1 + 48)) := by
    intro x hx
    simp only [Region.Contains] at hx ⊢
    have := h.fit; have := h.stk
    bv_omega
  rw [h.wr] at hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl
  exact h.b_c.sub_left hs

omit hv hd hK ho hl hc in
theorem EPre.covers {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    Covers (rdC p off len σ ++ wrC p σ) (σ.rd ++ σ.wr) ∧ Covers (wrC p σ) σ.wr := by
  rw [h.rd, h.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨reg (vPk σ) L, by simp, 0, by simp, by simpa using hL⟩
    · exact ⟨reg (vMu σ) 64, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (vSg σ) p.sigLen, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (vPk σ) L, by simp, off, rfl, hoff⟩
    · exact ⟨reg (vScr σ) (scrLen p), by simp, 0, by simp, by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    exact ⟨reg (vScr σ) (scrLen p), by simp, 0, by simp, by simp⟩

/-- An entry: the kernel's result, from the inputs our caller gave. -/
theorem entryV_wp {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    WP isa (entryCode (eMv off len) name code) σ fun s' => PPC64LE.target.abiPreserved σ s' ∧
      (((s'.gpr .r3).setWidth 32 = 1 ∧ ∃ b, vv p σ b = some true) ∨
        ((s'.gpr .r3).setWidth 32 = 0 ∧ vv p σ minBounds ≠ some true)) := by
  obtain ⟨cv, cw⟩ := h.covers hL hoff
  refine entry_wp (name := name) (F := eF off len) (R := fun _ r => (r.setWidth 32 = 1 ∧ ∃ b, vv p σ b = some true) ∨
      (r.setWidth 32 = 0 ∧ vv p σ minBounds ≠ some true)) hv.1 (by omega) (eMv_ok ho hl) (eF_ok off len)
    (by have := h.stk; omega) h.hd96
    (kpre_to (cs_kpre h hL hoff (by omega) (by omega) (hc σ h))) cv cw fun s' hq => ?_
  have q := hq
  generalize hτ : cs p off len σ = τ at q
  sig_post [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs] at q
  subst hτ
  obtain ⟨k₁, m₁, r₁⟩ := h.inputs (off := off) (len := len) hL
  simp only [vv]
  rw [← k₁, ← m₁, ← r₁]
  exact q

/-- Two runs of an entry leak the same if their entry states agree on the
inputs' leakage, the pointers and the stack pointer. -/
theorem entryV_tr {P : State → State → Prop}
    (hP : ∀ x y, P x y → EPre p L (K + 1 + 48) X x ∧ EPre p L (K + 1 + 48) X y ∧ x.sp = y.sp ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6], x.gpr r = y.gpr r) ∧
      leakBytes (pkOf p x ++ muOf x ++ sgOf p x) =
        leakBytes (pkOf p y ++ muOf y ++ sgOf p y)) :
    RelCT isa P (entryCode (eMv off len) name code) fun _ _ => True := by
  refine entry_tr (name := name) (F := eF off len) (rd := rdC p off len) (wr := wrC p) hv.1 (by omega)
    (eMv_ok ho hl) (eF_ok off len) hv.2.1 rfl (fun x y h => (hP x y h).2.2.1) (fun x ⟨y, hxy⟩ => ?_)
    (fun x y hxy => ?_)
  · have hx : EPre p L (K + 1 + 48) X x := by
      rcases hxy with h | h
      exacts [(hP x y h).1, (hP y x h).2.1]
    obtain ⟨cv, cw⟩ := hx.covers hL hoff
    exact ⟨by have := hx.stk; omega, hx.hd96,
      kpre_to (cs_kpre hx hL hoff (by omega) (by omega) (hc x hx)), cv, cw⟩
  · obtain ⟨hx, hy, hsp, hreg, hlk⟩ := hP x y hxy
    have g : ∀ {r : Reg}, r ∈ [Reg.r3, .r4, .r5, .r6] →
        (cs p off len x).gpr r = (cs p off len y).gpr r := fun {r} hr => by
      have : r ≠ .r0 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r11 ∧ r ≠ .r12 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [cs_gpr x this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2,
        cs_gpr y this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hreg r hr]
    obtain ⟨k₁, m₁, r₁⟩ := hx.inputs (off := off) (len := len) hL
    obtain ⟨k₂, m₂, r₂⟩ := hy.inputs (off := off) (len := len) hL
    have e7 : (cs p off len x).gpr .r7 = (cs p off len y).gpr .r7 := by rw [cs_r7, cs_r7, hreg .r3 (by simp)]
    have e8 : (cs p off len x).gpr .r8 = (cs p off len y).gpr .r8 := by rw [cs_r8, cs_r8]
    have esp : (cs p off len x).sp = (cs p off len y).sp := by rw [cs_sp, cs_sp, hsp]
    have elk : leakBytes (pkOf p (cs p off len x) ++ muOf (cs p off len x) ++
        sgOf p (cs p off len x)) = leakBytes (pkOf p (cs p off len y) ++
        muOf (cs p off len y) ++ sgOf p (cs p off len y)) := by
      rw [k₁, m₁, r₁, k₂, m₂, r₂]; exact hlk
    have g3 := g (r := .r3) (by simp)
    have g4 := g (r := .r4) (by simp)
    have g5 := g (r := .r5) (by simp)
    have g6 := g (r := .r6) (by simp)
    show (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (K + 1)).pub (cs p off len x) (cs p off len y)
    simp only [pkOf, muOf, sgOf, vPk, vMu, vSg] at elk
    generalize cs p off len x = X' at *
    generalize cs p off len y = Y' at *
    sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig,
      PPC64LE.abi, PPC64LE.argRegs]
    exact ⟨esp, elk, g3, g4, g5, g6, e7, e8⟩

end

/-! ## `vg_mldsa*_verify` and `vg_mldsa*_verify_prepared` -/

/-- A state that satisfies `verifyContract`'s precondition, for the contract's satisfiability. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scrLen p⟩]

section
variable {p : Params} {K : Nat} {name : String} {code : Prog isa}
  (hv : Verified PPC64LE.target code (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (K + 1)))
  (hd : sdepth code ≤ K + 1) (hK : K + 1 + 48 < 2 ^ 64)
include hv hd hK

omit hv hd hK in
/-- The public data of the entries' contracts, for `entryV_tr`. -/
theorem pub_of {L : Nat} {X : State → Prop} {x y : State} (hx : EPre p L (K + 1 + 48) X x)
    (hy : EPre p L (K + 1 + 48) X y) (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6)
    (hl : leakBytes (pkOf p x ++ muOf x ++ sgOf p x) =
      leakBytes (pkOf p y ++ muOf y ++ sgOf p y)) :
    EPre p L (K + 1 + 48) X x ∧ EPre p L (K + 1 + 48) X y ∧ x.sp = y.sp ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6], x.gpr r = y.gpr r) ∧
      leakBytes (pkOf p x ++ muOf x ++ sgOf p x) =
        leakBytes (pkOf p y ++ muOf y ++ sgOf p y) := by
  refine ⟨hx, hy, hsp, fun r hr => ?_, hl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h3, h4, h5, h6]

/-- `vg_mldsa*_verify`: the kernel with no cache. -/
theorem verify_entry_verified (hsat : ∃ s, (verifyContract p PPC64LE.abi (K + 1 + 48)).pre s) :
    Verified PPC64LE.target (entry p name code false) (verifyContract p PPC64LE.abi (K + 1 + 48)) := by
  have hE (σ : State) (h : (verifyContract p PPC64LE.abi (K + 1 + 48)).pre σ) :
      EPre p p.pkLen (K + 1 + 48) (fun _ => True) σ := epre_verify (k := K + 48) h
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · refine WP.mono (entryV_wp (name := name) hv hd hK (Nat.le_refl _) (off := 0) (len := 0) (by omega) (by decide)
      (by decide) (fun _ _ => .inl rfl) (hE σ hs)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    sig_post [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs]
    exact hq
  · refine (entryV_tr (name := name) (X := fun _ => True) hv hd hK (Nat.le_refl _) (off := 0) (len := 0) (by omega)
      (by decide) (by decide) (fun _ _ => .inl rfl) (P := fun x y => (verifyContract p PPC64LE.abi (K + 1 + 48)).pre x ∧
        (verifyContract p PPC64LE.abi (K + 1 + 48)).pre y ∧ (verifyContract p PPC64LE.abi (K + 1 + 48)).pub x y)
      (fun x y ⟨a, b, c⟩ => ?_) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
    sig_pub [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs] at c
    obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := c
    exact pub_of (hE x a) (hE y b) hsp h3 h4 h5 h6 hl

omit hv hd hK in
/-- The polynomials a prepared public key holds after its encoded key, as a cache. -/
theorem prepared_cache {m : Mem} {key : Addr} (h : PreparedPublicKey p m key) :
    Proof.MlDsa.CachedPublicPolys p m (key + BitVec.ofNat 64 p.pkLen) (bytesAt m key p.pkLen) := fun i hi => by
  have := Proof.MlDsa.polyStored_iff.mp (h i hi)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

/-- `vg_mldsa*_verify_prepared`: the kernel with the polynomials of a prepared public key. -/
theorem prepared_entry_verified (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (hsat : ∃ s, (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)).pre s) :
    Verified PPC64LE.target (entry p name code true)
      (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)) := by
  have hE (σ : State) (h : (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)).pre σ) :
      EPre p (preparedPublicKeyBytes p) (K + 1 + 48) (fun σ => PreparedPublicKey p σ.mem (vPk σ)) σ :=
    epre_prepared (k := K + 48) h
  have hL : p.pkLen ≤ preparedPublicKeyBytes p := by simp only [preparedPublicKeyBytes]; omega
  have hoff : p.pkLen + 1024 * p.k ≤ preparedPublicKeyBytes p := by
    simp only [preparedPublicKeyBytes]; show _ ≤ _ + 4 * 256 * _; omega
  have ho : p.pkLen < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hl : 1024 * p.k < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hc : ∀ σ, EPre p (preparedPublicKeyBytes p) (K + 1 + 48) (fun σ => PreparedPublicKey p σ.mem (vPk σ)) σ →
      1024 * p.k = 0 ∨ (1024 * p.k = 4 * n * p.k ∧
        Proof.MlDsa.CachedPublicPolys p σ.mem (vPk σ + BitVec.ofNat 64 p.pkLen) (pkOf p σ)) :=
    fun σ h => .inr ⟨by show _ = 4 * 256 * _; omega, prepared_cache h.x⟩
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · refine WP.mono (entryV_wp (name := name) hv hd hK hL hoff ho hl hc (hE σ hs)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    sig_post [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs]
    exact hq
  · refine (entryV_tr (name := name) hv hd hK hL hoff ho hl hc
      (P := fun x y => (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)).pre x ∧
        (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)).pre y ∧
        (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (K + 1 + 48)).pub x y)
      (fun x y ⟨a, b, c⟩ => ?_) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
    sig_pub [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs] at c
    obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := c
    exact pub_of (hE x a) (hE y b) hsp h3 h4 h5 h6 hl

end

end VG.Proof.MlDsa.PPC64LE.Verify
