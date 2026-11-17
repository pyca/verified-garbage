module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Cand
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ecdsa.Rfc6979.Arm.Loop`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.Arm.Core`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: signing with a candidate

`core(out, d, X, k, scratch)`'s arguments (`coreArgs_ok`), then the
call of `vg_ecdsa_<curve>_sign_k` with `X` (or, if `big`, the digest at
`fXc`) and `k = T` from the frame, in a frame of `{r12, lr}`
whose first word is its stack argument, `scratch`, as for HMAC's `init`
(`core_ok`): it returns 1 and writes the signature, or returns 0 and writes
zeros, as `Spec.Ecdsa.signWith` gives for `d` and `Q` bytes of the digest
and of `k`, and changes only `out`, `scratch` and the 24 bytes below the
frame.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Arm.FrameStack
open VG.Proof.Pbkdf2.Whole.Arm (After stk frame2_ok p2_arg0 p2_bytes p2_sub)
open VG.Proof.Pbkdf2.Stream.Arm (ce0 ce1 ce2 ce3)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The digest and `k` `core` is passed, and their addresses. -/
abbrev dgArg (P : RfcHash) {dn : Nat} (L : Lay dn) : BitVec 32 := L.fp + BitVec.ofNat 32 (cfgOf P).fDg
abbrev kArgV {dn : Nat} (L : Lay dn) : BitVec 32 := L.fp + BitVec.ofNat 32 fT
abbrev dgAddr (P : RfcHash) {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (24 + (cfgOf P).fDg)

theorem fDg_le (P : RfcHash) : 192 ≤ (cfgOf P).fDg ∧ (cfgOf P).fDg ≤ 260 := by
  simp only [Cfg.fDg]; split <;> simp [fX, fXc]

theorem dgArg_w (hL : L.Ok) : State.addr (dgArg P L) = dgAddr P L :=
  hL.fpA (by have := fDg_le P; omega_arith)

theorem kArg_w (hL : L.Ok) : State.addr (kArgV L) = kArg L := hL.fpA (by decide)

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m (State.addr L.d) (dgAddr P L) (kArg L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and its
argument on the stack, and writes `out` and `scratch`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨State.addr L.d, P.Q⟩, ⟨dgAddr P L, P.Q⟩, ⟨kArg L, P.Q⟩, ⟨L.B + BitVec.ofNat 64 16, 4⟩] ++ L.TBLs
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨State.addr L.out, 2 * P.Q⟩, L.SCR]

/-- The arguments of `core`. -/
theorem coreArgs_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = L.out ∧ t'.gpr .r1 = L.d ∧ t'.gpr .r2 = dgArg P L ∧ t'.gpr .r3 = kArgV L ∧
      t'.gpr .r12 = L.scr ∧ t'.gpr .r9 = t.gpr .r9 := by
  obtain he : encodable (BitVec.ofNat 32 (cfgOf P).fDg) = true := by
    simp only [Cfg.fDg]; split <;> decide
  simp only [Cfg.coreArgs]
  refine movr_ok hc (d := .r0) (r := .r4) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine movr_ok c₁ (d := .r1) (r := .r5) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  obtain h0 : t₂.gpr .r0 = L.out := by rw [k₂ _ (by decide), v₁, hc.r4]
  obtain h1 : t₂.gpr .r1 = L.d := by rw [v₂, c₁.r5]
  obtain h9 : t₂.gpr .r9 = t.gpr .r9 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  obtain m : t₂.mem = t.mem := by rw [m₂, m₁]
  refine fpAdd_ok c₂ (d := .r2) (by decide) (o := (cfgOf P).fDg) he fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine fpAdd_ok c₃ (d := .r3) (by decide) (o := fT) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine movr_ok c₄ (d := .r12) (r := .r11) (by decide) fun t₅ c₅ m₅ v₅ k₅ => WP.block_nil ?_
  refine ⟨c₅, by rw [m₅, m₄, m₃, m], ?_, ?_, ?_, ?_, by rw [v₅, c₄.r11], ?_⟩
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h0]
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h1]
  · rw [k₅ _ (by decide), k₄ _ (by decide), v₃]
  · rw [k₅ _ (by decide), v₄]
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h9]

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs (P : RfcHash) {dn : Nat} (L : Lay dn) (t : State) : Prop where
  r0 : t.gpr .r0 = L.out
  r1 : t.gpr .r1 = L.d
  r2 : t.gpr .r2 = dgArg P L
  r3 : t.gpr .r3 = kArgV L
  r12 : t.gpr .r12 = L.scr

/-- What the proof needs of the layout: scalars of `Q` bytes, the curve's
tables of constants, and the table of `P`'s hash function and functions. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ L.cs = P.R.coreConsts ∧ TabL P L ∧ P.F.H.D ≤ dn

/-- `core`'s digest and `k`: in the frame, apart from `out`, `scratch` and
the stack below the frame, and not wrapping. -/
theorem coreArg_ok (hL : L.Ok) {v : BitVec 32} {x : Addr}
    (hx : (v = dgArg P L ∧ x = dgAddr P L) ∨ (v = kArgV L ∧ x = kArg L)) :
    (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B, 24⟩ ∧ v.toNat + P.Q ≤ 2 ^ 32 := by
  have nB := hL.nB
  have := L.sp.isLt
  have := hL.na
  obtain hf := fDg_le P
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩, hL.stk_OUT (by omega_arith),
      hL.stk_SCR (by omega_arith), (Offset.base_disjoint _ (by omega_arith) (by omega_arith)).symm,
      by rw [fp_toNat hL (by omega_arith)]; omega_arith⟩
  · exact ⟨⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩, hL.stk_OUT (by omega_arith),
      hL.stk_SCR (by omega_arith), (Offset.base_disjoint _ (by omega_arith) (by omega_arith)).symm,
      by rw [fp_toNat hL (by decide)]; simp only [fT]; omega_arith⟩

theorem core_sp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    State.addr (t.sp - BitVec.ofNat 32 8) = L.B + BitVec.ofNat 64 16 := by
  rw [addr_sub' (by have := hc.sp24 hL; omega_arith), hc.spA hL, Offset.add_ofNat_sub _ (by decide)]

/-- The nested call preserves the table-address environment. -/
theorem core_syms {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    {c : String × List (BitVec 64)} (h : c∈L.cs) :
    ((pushed [.r12,.lr] t).callEntry.withRegions rd wr).syms c.1=L.sy c.1 := hc.sy c h

theorem core_tbls (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region} :
    Abi.constRegions (fun n => State.addr (((pushed [.r12,.lr] t).callEntry.withRegions rd wr).syms n))
      P.R.coreConsts=L.TBLs := by
  rw [← hk.2.1]
  apply List.map_congr_left
  intro c hc'
  simp only [core_syms hc hc']

/-- The public ROM survives the RFC frame, its calls, and the core's argument push. -/
theorem core_tables (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    TablesOk P.R.coreConsts
      (((pushed [.r12,.lr] t).callEntry.withRegions (coreRd P L) (coreWr P L)).syms)
      (((pushed [.r12,.lr] t).callEntry.withRegions (coreRd P L) (coreWr P L)).mem)
      (coreWr P L) := by
  intro c hcc
  obtain hcs : c∈L.cs := hk.2.1 ▸ hcc
  have table : (⟨State.addr (L.sy c.1),8*c.2.length⟩ : Region)∈L.TBLs := List.mem_map_of_mem
    (f := fun c => (⟨State.addr (L.sy c.1),8*c.2.length⟩ : Region)) hcs
  obtain ht := hL.tables _ table
  obtain fit : 8*c.2.length≤2^64 := by dsimp only at ht; omega
  obtain hpushed : Frame [L.STK] t.mem (pushed [.r12,.lr] t).mem := by
    apply (pushed_frameA (rs := [.r12,.lr]) (s := t) (by change 8≤t.sp.toNat; have := hc.sp24 hL; omega_arith)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨L.STK,by simp,?_⟩
    obtain ea : belowA t.sp 8=⟨L.B+BitVec.ofNat 64 16,8⟩ := by
      change (⟨State.addr (t.sp-BitVec.ofNat 32 8),8⟩ : Region)=_
      rw [core_sp hL hc]
    change Region.Sub (belowA t.sp 8) L.STK
    rw [ea]
    exact Offset.sub_base _ (by omega_arith)
  obtain frame := hc.frame.trans (hpushed.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨L.STK,by simp,(fun _ h => h)⟩)
  simp only [core_syms hc hcs,State.withRegions_mem,State.callEntry_mem]
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rw [frame.readW (r := ⟨State.addr (L.sy c.1),8*c.2.length⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith)) ht.2.1 (by decide)]
    exact hc.held c hcs i hi
  · simpa only [toNat_addr] using ht.1
  · intro r hr
    simp only [coreWr,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · have e : (⟨State.addr L.out,2*P.Q⟩ : Region)=L.OUT := by rw [Lay.OUT,hk.1]
      rw [e]
      exact ht.2.1 _ (by simp)
    · exact ht.2.1 _ (by simp)
  · exact ht.2.2

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs P L t) :
    (coreK P.R.E P.R.coreConsts).pre ((pushed [.r12, .lr] t).callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  obtain h24 := hc.sp24 hL
  obtain hsp := core_sp hL hc
  have := hL.nB; have := L.sp.isLt
  have hq : L.q = P.R.E.C.len := hk.1
  obtain eD : (⟨State.addr L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  obtain eO : (⟨State.addr L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
  obtain ⟨-, gO, gS, -, gN⟩ := coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)
  obtain ⟨-, kO, kS, -, kN⟩ := coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)
  rw [coreK]
  simp only [State.withRegions_gpr, ce0, ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1,
    hr.r2, hr.r3, p2_arg0 (s := t) (by omega_arith), hr.r12, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, pushed_sp, dgArg_w hL, kArg_w hL]
  simp only [eD, eO]
  refine ⟨?_, trivial, hL.oc, hL.dc, gS, kS, ?_, ?_,
    by have := hL.no; rw [hq] at this; omega_arith, by have := hL.nd; rw [hq] at this; omega_arith, gN, kN, hL.nc, ?_,?_⟩
  · rw [core_tbls hk hc,← eD, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_OUT (by omega_arith)).symm
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_SCR (by omega_arith)).symm
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, VG.Arm.FrameStack.sub_toNat' (by omega_arith)]; omega_arith
  · have tab := core_tables hL hk hc
    obtain eqW : coreWr P L=[L.OUT,L.SCR] := by simp only [coreWr,Lay.OUT,hk.1]
    rw [eqW] at tab
    exact tab

theorem core_cov (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) := by
  have hq : L.q = P.Q := hk.1
  obtain hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
      ∃ R ∈ ([L.D, L.DG, L.TAB, L.ARGS] ++ L.TBLs) ++ [⟨L.B + BitVec.ofNat 64 16, 8⟩, L.FR, L.OUT, L.SCR],
        Within ⟨x, P.Q⟩ R :=
    fun ⟨R, hR, hW⟩ => ⟨R, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl <;> simp, hW⟩
  refine covers_of fun q hq' => ?_
  rw [pushed_rd, pushed_wr, hc.rd, hc.wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, core_sp hL hc]
  simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq'
  rcases hq' with rfl | rfl | rfl | rfl | htbl | rfl | rfl
  · exact ⟨L.D, by simp, within_base _ (by omega_arith)⟩
  · exact hw (coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)).1
  · exact hw (coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)).1
  · exact ⟨⟨L.B + BitVec.ofNat 64 16, 8⟩, by simp, within_base _ (by omega_arith)⟩
  · exact ⟨q,by simp [htbl],within_base q.base (Nat.le_refl q.len)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩

theorem core_covW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreWr P L) (pushed [.r12, .lr] t).wr :=
  covers_of fun q hq' => by
    rw [pushed_wr, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩

/-- `core(out, d, digest, k, scratch)`, in a frame of `{scratch, lr}`. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs P L t) :
    WP isa (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 1 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 0 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  apply WP.of_syms
  obtain h24 := hc.sp24 hL
  obtain hst := hc.stk_eq hL
  have hq : L.q = P.Q := hk.1
  obtain eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine frame2_ok (ra := .r12) (rb := .lr) (t := .r12) rfl (by decide) P.R.coreX
    (by show armStack P.R.coreC ≤ 16; rw [P.R.coreStack]; omega_arith) h24 (core_pre hL hk hc hr)
    (core_cov hL hk hc) (core_covW hq hc) fun s₂ mL uL hfl ha hpost syEnd => ?_
  rw [eW] at ha
  obtain hf : Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem mL := ha.frame.sub fun q hq' => by
    rw [hst] at hq'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
  refine ⟨hc.after hL ha (fun q hq' => ?_) syEnd, ha.cs .r9 (by decide) (by decide), hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
  · obtain ⟨-, -, -, gB, -⟩ := coreArg_ok (P := P) hL (.inl ⟨rfl, rfl⟩)
    obtain ⟨-, -, -, kB, -⟩ := coreArg_ok (P := P) hL (.inr ⟨rfl, rfl⟩)
    have hQe : P.Q = P.R.E.C.len := rfl
    obtain hQl : P.Q ≤ 72 := by have := P.wsizes.2.2.2.2.2.1; omega_arith
    have hq : L.q = P.Q := hk.1
    obtain hs : coreSigOf P.R.E (pushed [.r12, .lr] t).mem (State.addr L.d) (dgAddr P L) (kArg L) =
        coreSig P L t.mem := by
      obtain d1 : (stk t).Disjoint ⟨State.addr L.d, P.R.E.C.len⟩ := by
        rw [hst]
        exact (hL.kd.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
      obtain d2 : (stk t).Disjoint ⟨dgAddr P L, P.R.E.C.len⟩ := by rw [hst]; exact gB.symm
      obtain d3 : (stk t).Disjoint ⟨kArg L, P.R.E.C.len⟩ := by rw [hst]; exact kB.symm
      simp only [coreSigOf, coreSig, Rfc6979.ecdsa_bytesAt]
      rw [p2_bytes h24 d1 (by omega_arith), p2_bytes h24 d2 (by omega_arith), p2_bytes h24 d3 (by omega_arith)]
    simp only [coreK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0,
      ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1, hr.r2, hr.r3, dgArg_w hL, kArg_w hL, hs] at hpost
    obtain dO : ∀ r ∈ [stk t], (⟨State.addr L.out, 2 * P.Q⟩ : Region).Disjoint r := fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [hst, ← hq]
      exact (hL.ko.sub_left (Region.sub_prefix (by omega_arith))).symm
    obtain bO : Spec.Sha256.bytesAt mL (State.addr L.out) (2 * P.Q) =
        Spec.Sha256.bytesAt s₂.mem (State.addr L.out) (2 * P.Q) :=
      List.map_congr_left fun _ hi => hfl.bytes dO
      (by show 2 * P.Q ≤ 2 ^ 64; have := P.wsizes.2.2.2.2.2.1; omega_arith) (List.mem_range.mp hi)
    dsimp only
    rw [popped_gpr (by decide), popped_gpr (by decide), bO]
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end


/-!
# Deterministic ECDSA on 32-bit ARM: the candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Loop.lean`): the values of a run,
as RFC 6979 computes them from the private key and the digest on entry
(`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the loop's invariant
before candidate `i` (`LoopInv`): `K` and `V` are those before it, the count
in `r9` is `tries - i`, every earlier candidate was unsuitable, and `core`'s
digest is the digest's (`DgOk`). One iteration either moves to candidate
`i + 1`, branching back, or leaves the loop with the signature of candidate
`i`, which is suitable or the last (`tryOne_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.ok.hH.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.ok.hH.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgAddr P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .r0 = 1 ∧ Spec.Sha256.bytesAt t.mem (State.addr L.out) (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => t.gpr .r0 = 0 ∧ Spec.Sha256.bytesAt t.mem (State.addr L.out) (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : t.gpr .r9 = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem (State.addr L.d) n = Spec.Sha256.bytesAt m₀ (State.addr L.d) n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem (State.addr L.dg) n = Spec.Sha256.bytesAt m₀ (State.addr L.dg) n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega_arith)

/-- What `core` changes: `out`, `scratch` and the stack below the frame. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B, 24⟩]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  have := hL.B_fit
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint_base _ h₁ (by omega_arith)

/-- The regions the loop writes, which are apart from `core`'s digest. -/
def DgApart {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 152⟩ ∨ r = ⟨L.B, 24⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 352, 140⟩

theorem dg_apart (hL : L.Ok) {r : Region} (h : DgApart L r) : Region.Disjoint ⟨dgAddr P L, P.Q⟩ r := by
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hb := hL.B_fit
  obtain hf := fDg_le P
  obtain hf' : (cfgOf P).fDg + P.Q ≤ 328 := by
    cases hb : P.R.big
    · have := P.sizesA hb; simp only [Cfg.fDg, cfgOf, hb, Bool.false_eq_true, ite_false, fX]; omega_arith
    · simp only [Cfg.fDg, cfgOf, hb, ite_true, fXc]; omega_arith
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact hL.stk_SCR (by omega_arith)
  · exact hL.stk_OUT (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

theorem DgOk.frame {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨dgAddr P L, P.Q⟩ r) : DgOk P L m₀ m' := by
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  unfold DgOk; rw [bytesAt_frame hf hd (by omega_arith)]; exact h

theorem DgOk.frameOf (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, DgApart L r) : DgOk P L m₀ m' :=
  h.frame hf fun r hr => dg_apart hL (hd r hr)

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 32 (T - i) - 1 = BitVec.ofNat 32 (T - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega_arith

theorem cnt_ne {T i : Nat} (hT : T < 2 ^ 16) : BitVec.ofNat 32 (T - (i + 1)) ≠ 0 ↔ i + 1 < T := by
  rw [Ne, ← BitVec.toNat_inj]
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h0]
  omega_arith

theorem low_word (h l : BitVec 32) : BitVec.setWidth 32 (h ++ l) = l := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt l.isLt, Nat.shiftLeft_eq]
  have := l.isLt
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt this]

/-- `core`'s signature is the candidate's: it reads the private key, its
digest, and `k`, whose number is `bits2int` of the candidate. -/
theorem coreSig_eq (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  obtain e₄ : Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q = Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q :=
    hc.dBytes hL (by rw [hk.1])
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, xOf]
  rw [show Spec.Sha256.bytesAt t.mem (dgAddr P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (dgAddr P L) P.Q from rfl,
    hdg, show Spec.Sha256.bytesAt t.mem (State.addr L.d) P.R.E.C.len =
      Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q from rfl, e₄,
    show Spec.Sha256.bytesAt t.mem (kArg L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (kArg L) P.Q from rfl, hkv]

theorem ResultIs.r0_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    t.gpr .r0 = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `r0` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .r0 = t.gpr .r0)
    (hm : Spec.Sha256.bytesAt t'.mem (State.addr L.out) (2 * P.Q) =
      Spec.Sha256.bytesAt t.mem (State.addr L.out) (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

theorem kvw_apart : ∀ r ∈ KVW L, DgApart L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem cw_apart : ∀ r ∈ CW L, DgApart L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem corew_apart : ∀ r ∈ CoreW L, DgApart L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : u.gpr .r9 = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : u.gpr .r9 = BitVec.ofNat 32 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : u.gpr .r9 = BitVec.ofNat 32 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval .ne u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem try₁_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hk.2.2.1 hc) fun u₁ ⟨hc₁, h9₁, hf₁, hk₁, hv₁, hb₁⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], h9₁.trans hi.cnt, hi.fails, hi.dg.frameOf hL hf₁ cw_apart,
    by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ CoreRegs P L u :=
  WP.mono (coreArgs_ok hc) fun _ ⟨hc₂, hm₂, h0, h1, h2, h3, h12, h9⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, h9.trans hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩,
      ⟨h0, h1, h2, h3, h12⟩⟩

theorem try₃_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : CoreRegs P L t) :
    WP isa (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) t
      fun u => Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  obtain hD := (P.shape P.hDB)
  refine WP.mono (core_ok (P := P) hL hk hc ha) fun u₃ ⟨hc₃, h9₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hk hc hi.dg hi.kk, low_word] at hr₃
  refine ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by omega_arith) (by anums)) (by anums)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by omega_arith) (by anums)) (by anums)).trans hi.v, h9₃.trans hi.cnt,
    hi.fails, hi.dg.frameOf hL hf₃ corew_apart, ?_⟩
  unfold ResultIs
  cases hs : sigI P L m₀ i <;> rw [hs] at hr₃ <;> exact hr₃

theorem try₄_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hm₄, h9₄, h0₄, _, hz₄⟩ =>
    ⟨hc₄, hi.lt, hm₄ ▸ hi.k, hm₄ ▸ hi.v, by rw [h9₄, hi.cnt, cnt_sub hi.lt], hi.fails, hm₄ ▸ hi.dg,
      hi.res.keep h0₄ (by rw [hm₄]), ?_⟩
  rw [hz₄, hi.cnt, cnt_sub hi.lt]
  simp only [hi.res.r0_zero, cnt_ne P.tries_lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite .ne (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL hk.2.2.1 (by rw [hk.1]) hc) fun u₅ ⟨hc₅, h9₅, hf₅, hk₅, hv₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, h9₆, hz₆⟩ => ⟨hc₆, .inr ⟨hz₆, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [h9₆, h9₅, hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [hm₆]; exact hi.dg.frameOf hL hf₅ kvw_apart
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, ha₅, hz₅⟩ => ⟨hc₅, .inl ⟨hz₅,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega_arith)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hk hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hk h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hk h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end


/-!
# Deterministic ECDSA on 32-bit ARM: correctness

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Correct.lean`): the loop leaves it
at a candidate that is suitable or the last (`tries_ok`); before it, `h`,
`K`, `V`, `core`'s digest and the count are as RFC 6979's steps a–g make
them (`stageX_ok` … `stageE_ok`); and the signature of that candidate is
RFC 6979's (`result_eq`), for the hash function `P`'s instance of the
contract with the table of its HMAC functions (`tabFacts`). The frame's
allocation, and our caller's registers saved in it and restored, give the
whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.X25519.Arm (wp_mov wp_str wp_ldr op2_reg)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  obtain hn1 : 1 ≤ n := by have := hi.lt; omega_arith
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_arith, hc', ?_, by omega_arith⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_arith]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by show 8 * P.R.E.C.len < _; omega_arith)

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  obtain hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega_using [h]), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega_using [h]) hn).1]

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) P.Q =
    List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.F.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  obtain hdg : Spec.Sha256.bytesAt u.mem (State.addr L.dg) (min P.F.H.D P.Q) =
      (hBOf P L m₀).take (min P.F.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega_using []), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hk.2.2.1 hk.2.2.2 hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by rw [QX, hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hk : CoreOk P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  have hbf := hL.B_fit
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  obtain hlB : (hBOf P L m₀).length = P.F.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    obtain ⟨hQk, -, hQ64⟩ := P.sizesA hb
    obtain hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xA L) P.Q) = eOf P L m₀ := by
      rw [show xA L = L.B + BitVec.ofNat 64 216 from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 24 + fH = hB from rfl]
      rw [← hQk] at hh₂
      rw [← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 hB) P.Q), length_bytesAt, hh₂, hX,
        hSpec, Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      rw [show dgAddr P L = L.B + BitVec.ofNat 64 216 by
        simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false, fX]]
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hQ66]) (by omega_using [])
          · exact Offset.disjoint _ (.inr (by simp only [hB]; omega_using [hQ66, hQk])) (by omega_using [hQ66]) (by simp only [hB]; omega_arith))
          (by omega_using [hQ66]),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', -, hQD⟩ := P.sizesW hb
    obtain hN : 8 * P.F.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.F.H.D < P.R.E.C.len := hQD
      omega_using [hl, this]
    obtain hm : min P.F.H.D P.Q = P.F.H.D := Nat.min_eq_left (by omega_using [hD64, hQ66'])
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hk.2.2.1 hb hk.2.2.2 hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        show 24 + fX = 216 from rfl,
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by omega_using [hQ66]) (by decide)
          · exact Offset.disjoint _ (.inl (by omega_using [hQ66])) (by omega_using [hQ66]) (by omega_using [])) (by omega_using [hQ66]),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
          (by show 8 * P.R.E.C.len < _; omega_using [hl]) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      obtain e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      obtain hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_using []) (by simp only [RfcHash.Q]; omega_using [hl, hN])
      obtain hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      rw [show dgAddr P L = L.B + BitVec.ofNat 64 284 by
        simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = true from hb, ite_true, fXc]]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl]) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = ⟨L.B, 152⟩ ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 152) :
    hOf P L m' = hOf P L m := by
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hbf := hL.B_fit
  obtain hho : 152 ≤ 24 + (cfgOf P).fHo ∧ 24 + (cfgOf P).fHo + P.Q ≤ 284 := by
    cases hb : P.R.big
    · have := P.sizesA hb
      simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false, fH]; omega_using [hQ66]
    · simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true, fX]; omega_using [hQ66]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hQ66])
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by omega_using [hho])
  · exact Offset.disjoint_base _ hho.1 (by omega_using [hho])
  · exact Offset.disjoint _ (.inr (by omega_using [hho, hon])) (by omega_using [hho]) (by omega_using [hon])

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have hbf := hL.B_fit
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨24, 128, rfl, by omega_using []⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frame hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dg_apart hL (r := ⟨L.B, 152⟩) (.inr (.inr (.inl rfl)))).sub_right
          (Offset.sub_base _ (by omega_using []))⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.1 (by rw [hk.1]) hc (b := 0) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.1 (by rw [hk.1]) hc (b := 1) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hc) fun u' ⟨hc', hm', hn'⟩ => ⟨hc', P.tries_pos, hm' ▸ hq.k, hm' ▸ hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hm' ▸ hq.dg⟩

/-- After the wiping: the result, and our caller's registers. -/
structure Fin (P : RfcHash) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop where
  sp : u.sp = L.fp
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, u.gpr p.1 = g p.1
  exit : ∃ i, Exit P L m₀ i u

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) : WP isa Cfg.wipe u (Fin P L g m₀) := by
  have hbf := hL.B_fit
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  exact WP.mono (wipe_ok hL hc) fun _ ⟨_, _, hsp, hs, ha, hf⟩ => ⟨hsp.trans hc.sp, hs, i,
    hx.lt, hx.fails, hx.last, hx.res.keep ha (bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (d := 24) (n := 4 * wipeWords) (by decide)).symm.sub_left
        (Region.sub_prefix (by rw [hk.1]))) (by omega_using [hQ66]))⟩

/-- The body, after the prologue. -/
theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV) (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne)
        Cfg.wipe))))))) t (Fin P L g m₀) :=
  WP.seq (WP.mono (stageX_ok hL hk hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hk h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk h₅ q₅) fun _ ⟨h₆, _, q₆⟩ => stageG_ok hL hk h₆ q₆)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ (State.addr L.d) (State.addr L.dg) =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ (State.addr L.d) (State.addr L.dg)).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_arith) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      obtain h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_arith]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## The entry -/

/-- What the contract says of the table at `stackArg s 1`: it holds `F`'s
HMAC functions, which an indirect call of `f`'s reaches, then its digest
length and HMAC's block size. -/
def tabFacts (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns) (s : State) : Prop :=
  TabOK F f s.syms ∧ TabMem F s.syms (stackArg s 1) s.mem ∧
    s.mem.readW (tA (stackArg s 1) tD) 32 = BitVec.ofNat 32 F.H.D ∧
    s.mem.readW (tA (stackArg s 1) tB) 32 = BitVec.ofNat 32 F.H.B

/-- The layout of a call from `s`. -/
def lay (dn q : Nat) (cs : List (String × List (BitVec 64))) (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns)
    (s : State) : Lay dn where
  out := s.gpr .r0
  d := s.gpr .r1
  dg := s.gpr .r2
  scr := stackArg s 0
  tab := stackArg s 1
  sp := s.sp
  q := q
  cs := cs
  sy n := if n ∈ cs.map Prod.fst then s.syms n else 0
  F := F
  f := f
  fa n := if n ∈ [F.hiN, F.H.updN, F.hfN] then s.syms n else 0

section
variable {dn q : Nat} {cs : List (String × List (BitVec 64))} {F : Impl.Pbkdf2.Whole.Arm.Fns} {f : Fns}

theorem lay_sy (s : State) {c : String × List (BitVec 64)} (hc : c ∈ cs) :
    (lay dn q cs F f s).sy c.1 = s.syms c.1 := by
  simp only [lay, List.mem_map_of_mem hc, ↓reduceIte]

theorem lay_tbls (s : State) :
    (lay dn q cs F f s).TBLs = Abi.constRegions (fun n => State.addr (s.syms n)) cs := by
  apply List.map_congr_left
  intro c hc
  simp only [lay_sy (dn := dn) (q := q) (cs := cs) (F := F) (f := f) s hc]

theorem lay_ok {I : Proof.Ecdsa.Rfc6979.Instance} {ns : List String} {s : State}
    (h : (rfcArm I stackT cs (tabFacts F f) ns).pre s) : (lay I.hashLen I.ecdsa.curve.len cs F f s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB, na, ao, ac, nt, to, tc, tk, tables, -⟩ := h
  refine ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nt, to, tc, tk, ao, ac, nB, na, ?_⟩
  intro r hr
  rw [lay_tbls] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain tc := tables c hc
  refine ⟨?_, tc.2.2.1, tc.2.2.2⟩
  simpa only [toNat_addr] using tc.2.1
end

/-- Words stored at offsets apart from a range below them change nothing outside it. -/
theorem Outs.frame {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {n : Nat}
    (h : VG.Proof.Mont.Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ n) : Frame [⟨base, n⟩] m m' :=
  fun x hx => h x fun r hr' => .inr (by
    have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [VG.Proof.Mont.ofs]
    have := hr r hr'; omega_arith)

theorem saved_ne12 : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, p.1 ≠ .r12 := by decide

theorem saved_pairwise : Impl.Ecdsa.Rfc6979.Arm.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  decide

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcArm P.I stackT P.R.coreConsts (tabFacts P.F P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.R.coreConsts P.F P.f s

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layOf P s) :=
  ⟨P.curveLen, rfl, ⟨rfl, rfl⟩, by rw [P.len]⟩

theorem fp_arg {s : State} {o : Nat} :
    (layOf P s).fp + BitVec.ofNat 32 (512 + o) = s.sp + BitVec.ofNat 32 o := by
  apply BitVec.eq_of_toNat_eq
  have := s.sp.isLt
  simp only [Lay.fp, layOf, lay, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- The prologue: our caller's registers into the frame, and the pointers to the registers that keep them. -/
theorem entry_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (.block Cfg.prologue) (allocated frameBytes s) (Ctx (layOf P s) s.gpr s.mem) := by
  apply WP.of_syms
  obtain hL : (layOf P s).Ok := lay_ok h
  have hN : 536 ≤ s.sp.toNat := hL.nB
  have hna : s.sp.toNat + 8 ≤ 2 ^ 32 := hL.na
  have htf : tabFacts P.F P.f s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have tables := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -⟩ := h
  have hA : State.addr (layOf P s).fp = (layOf P s).B + BitVec.ofNat 64 24 := hL.fpA0
  have hb := hL.B_fit
  have hBt : (layOf P s).B.toNat = s.sp.toNat - 536 := hL.B_toNat
  obtain hS : State.addr s.sp = (layOf P s).B + BitVec.ofNat 64 536 := Lay.Ok.spA (L := layOf P s)
  simp only [Cfg.prologue, List.cons_append]
  refine wp_addSp (d := .r12) (imm := 0) (by decide) fun u₁ v₁ => ?_
  obtain h12 : u₁.gpr .r12 = (layOf P s).fp := by rw [v₁.gpr, BitVec.add_zero]; rfl
  obtain hs : VG.Proof.Mont.Arm.Scr u₁ ((layOf P s).B + BitVec.ofNat 64 24) 512 :=
    ⟨by rw [h12, hA], ⟨512, Nat.le_refl _, by decide, by
      rw [v₁.wr]; show _ ∈ ⟨State.addr (layOf P s).fp, 512⟩ :: s.wr; rw [hA]; exact List.mem_cons_self⟩,
      by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by decide⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Weierstrass.Arm.strs_ok hs _ (fun p hp => by have := saved_off p hp; omega_arith)
    saved_pairwise) fun u₂ ⟨K₂, O₂, V₂⟩ => ?_
  obtain g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by rw [K₂.gpr r (by simp), v₁.other _ hr]; rfl
  obtain f₂ : Frame [(layOf P s).STK] s.mem u₂.mem := by
    rw [show s.mem = u₁.mem from v₁.mem.symm]
    refine (Outs.frame O₂ (n := 504) fun r hr => ?_).sub fun r hr => ?_
    · simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (saved_off q hq).2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_arith)⟩
  refine wp_mov (op2_reg _ _) fun u₃ v₃ => wp_mov (op2_reg _ _) fun u₄ v₄ => ?_
  obtain K₄ : VG.Proof.X25519.Arm.Rest [.r4, .r5] u₂ u₄ := (v₃.rest (by simp)).trans (v₄.rest (by simp))
  obtain h12₄ : u₄.gpr .r12 = (layOf P s).fp := by rw [K₄.gpr _ (by simp), K₂.gpr _ (by simp), h12]
  obtain hW : State.addr (u₄.gpr .r12 + BitVec.ofNat 32 fDigest) = (layOf P s).B + BitVec.ofNat 64 528 := by
    rw [h12₄, hL.fpA (by decide)]; rfl
  refine wp_str (by decide) hW ⟨(layOf P s).FR, by
      rw [K₄.wr, K₂.wr, v₁.wr]; show _ ∈ ⟨State.addr (layOf P s).fp, 512⟩ :: s.wr; rw [hA]; exact List.mem_cons_self,
    Offset.contains _ (by decide) (by decide) (by omega_arith)⟩ fun u₅ v₅ => ?_
  obtain m₅ : u₅.mem = u₂.mem.writeW ((layOf P s).B + BitVec.ofNat 64 528) (s.gpr .r2) := by
    rw [v₅.mem, v₄.mem, v₃.mem, K₄.gpr _ (by simp), g₂ _ (by decide)]
  obtain f₅' : Frame [⟨(layOf P s).B + BitVec.ofNat 64 528, 4⟩] u₂.mem u₅.mem := by
    rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f₅ : Frame [(layOf P s).STK] s.mem u₅.mem := by
    rw [m₅]; exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain hargs : ∀ o, o + 4 ≤ 8 → u₅.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun o ho => by
    rw [addr_add (by omega_arith), hS, Offset.add_add]
    exact f₅.readW (r := ⟨(layOf P s).B + BitVec.ofNat 64 536, 8⟩) (Offset.contains _ (by omega_arith)
      (by omega_arith) (by omega_arith)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega_arith)) (by decide)
  obtain h12₅ : u₅.gpr .r12 = (layOf P s).fp := by rw [v₅.gpr, h12₄]
  obtain hin : ∀ o, o + 4 ≤ 8 → InRegions (u₅.rd ++ u₅.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
    intro o ho
    refine ⟨(layOf P s).ARGS, ?_, ?_⟩
    · rw [v₅.rd, K₄.rd, K₂.rd, v₁.rd]
      show _ ∈ s.rd ++ _
      rw [hrd]
      exact List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · rw [addr_add (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine wp_ldr (by decide) (by rw [h12₅, show frameBytes = 512 + 0 from rfl, fp_arg])
    (hin 0 (by decide)) fun u₆ v₆ => ?_
  refine wp_ldr (by decide) (by rw [v₆.other _ (by decide), h12₅, show frameBytes + 4 = 512 + 4 from rfl,
    fp_arg]) (by rw [v₆.rd, v₆.wr]; exact hin 4 (by decide)) fun u₇ v₇ => ?_
  refine wp_mov (op2_reg _ _) fun u₈ v₈ => WP.block_nil (fun syEnd => ?_)
  obtain K₈ : VG.Proof.X25519.Arm.Rest [.r4, .r5, .r11, .r6, .r8] u₂ u₈ :=
    (K₄.mono (by simp)).trans <| (v₅.rest _).trans <| (v₆.rest (by simp)).trans <| (v₇.rest (by simp)).trans
      (v₈.rest (by simp))
  obtain hm : u₈.mem = u₅.mem := by rw [v₈.mem, v₇.mem, v₆.mem]
  refine ⟨by rw [K₈.rd, K₂.rd, v₁.rd, lay_tbls]; exact hrd, ?_, by rw [K₈.sp, K₂.sp, v₁.sp]; rfl, ?_, ?_, ?_, ?_, ?_,
    fun p hp => ?_, ?_, by rw [hm]; exact f₅.sub fun r hr => ⟨r, by simp at hr; simp [hr], sub_refl _⟩,
    fun c hc => by rw [syEnd]; exact (lay_sy s hc).symm, fun c hc i hi => ?_, by rw [syEnd]; exact htf.1,
    by rw [syEnd]; exact htf.2.1, htf.2.2.1, htf.2.2.2, fun n hn => by
      rw [syEnd]
      show s.syms n = (if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s.syms n else 0)
      exact (ite_eq_left_of_eq_true _ _ (eq_true hn)).symm⟩
  · rw [K₈.wr, K₂.wr, v₁.wr]
    show ⟨State.addr (layOf P s).fp, frameBytes⟩ :: s.wr = _
    rw [hA, hwr]
    rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide),
      v₃.gpr, g₂ _ (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.gpr,
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.gpr, v₆.mem, hargs 4 (by decide)]; rfl
  · rw [v₈.gpr, v₇.other _ (by decide), v₆.other _ (by decide), h12₅]
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, hargs 0 (by decide)]; rfl
  · have := saved_off p hp
    rw [hm, f₅'.readW (r := ⟨(layOf P s).B + BitVec.ofNat 64 (24 + p.2), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    obtain h₂ := V₂ p hp
    rw [VG.Proof.Mont.off, Offset.add_add] at h₂
    rw [h₂, v₁.other _ (saved_ne12 p hp)]; rfl
  · rw [hm, m₅, show 24 + fDigest = 528 from rfl, Mem.readW_writeW_self32]; rfl
  · change s.mem.readW (State.addr ((layOf P s).sy c.1) + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
    rw [lay_sy (cs := P.R.coreConsts) s hc]
    exact (tables c hc).1 i hi

theorem low_preserved : ∀ r ∈ preserved, r ∈ Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst := by decide

theorem frameBytes_ok :
    0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 frameBytes) = true := by
  decide

/-- `vg_ecdsa_<curve>_sign` for `P`'s hash function meets `rfcP P` and keeps
the callee-saved registers and the stack pointer. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcP P ns).post s s' := by
  obtain hL : (layOf P s).Ok := lay_ok h
  have hN : 536 ≤ s.sp.toNat := hL.nB
  obtain hk := coreOk_lay P s
  refine WP.alloc frameBytes_ok (by show 512 ≤ _; omega_arith) ?_
  rw [Cfg.body]
  refine WP.seq (WP.mono (entry_ok h) fun t hc => WP.mono (body_ok hL hk hc) fun v hv lm lu hfl => ?_)
  obtain ⟨hsp, hs, i, hx⟩ := hv
  obtain dO : ∀ r ∈ [(⟨State.addr (s.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ : Region)],
      (⟨State.addr (layOf P s).out, 2 * P.Q⟩ : Region).Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    show Region.Disjoint _ ⟨State.addr (layOf P s).fp, 512⟩
    rw [hL.fpA0, ← (coreOk_lay P s).1]
    exact (hL.ko.sub_left (Offset.sub_base _ (by decide))).symm
  obtain bO : Spec.Sha256.bytesAt lm (State.addr (layOf P s).out) (2 * P.Q) =
      Spec.Sha256.bytesAt v.mem (State.addr (layOf P s).out) (2 * P.Q) :=
    List.map_congr_left fun _ hi => hfl.bytes dO
      (by show 2 * P.Q ≤ 2 ^ 64; have := P.wsizes.2.2.2.2.2.1; omega_arith) (List.mem_range.mp hi)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (freed frameBytes v).gpr r = _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (low_preserved r hr)
    exact hs p hp
  · show v.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · show match (result P.I s.mem (State.addr (layOf P s).d) (State.addr (layOf P s).dg)).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    obtain e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    obtain e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    have hr := hx.res
    unfold ResultIs at hr
    show match sigI P (layOf P s) s.mem i with | some rs => _ | none => _
    cases hsig : sigI P (layOf P s) s.mem i <;> rw [hsig] at hr <;>
      exact ⟨by rw [low_word]; exact hr.1, bO.trans hr.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
