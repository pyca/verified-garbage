module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Cand
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Cand
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ecdsa.Rfc6979.Arm.CT`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.Arm.Correct`, which only this module used -/

section

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

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): the loop leaves it
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

end

end

/-!
# Deterministic ECDSA on 32-bit ARM: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the prologue and the frame's release they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs).
The blocks address only the frame and the buffers, from the registers that
hold the pointers, which agree (the taint analysis, of the blocks whose
contents depend on the curve: `RfcT`, each curve's `RfcCurve.blk`), or, for
the byte loops, from registers both runs set alike (`T`'s length, `D`); an
indirect call reaches, through the table, whose address `r6` holds, the
same function in both runs (`tcall_ct`), each of which is constant time with
arguments that agree (`hi_rel`, `upd_rel`, `hf_rel`, `frame2_rel`); and the
loop's branch agrees, since in both runs it goes on after candidate `i` iff
`i` is before the candidate it stops at (`go_iff`). The prologue's first
instruction reads `sp`, which agrees (`start_blk`), and the frame's
allocation and release access no memory (`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.AesGcm.Arm (copyLoop)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.X25519.Arm (op2_reg op2_imm dpVal)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.Pbkdf2.Whole.Arm (hi_rel hf_rel frame2_rel)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

/-! ## Frames and single instructions -/

/-- Allocating and freeing a buffer leaks no addresses. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- An instruction that leaks the same in two runs, then a block. -/
theorem block_cons_ct {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by rw [he], hq⟩

theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (τr rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 = 0 then P.I.tries - 1
  else (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {P : RfcHash} {L : Lay P.I.hashLen} {m₀ : Mem} {i : Nat} (hi : i < P.I.tries)
    (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_arith) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_arith]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_arith) (by omega_arith)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## Two runs -/

/-- What each of two runs has, between the prologue and the frame's release. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.I.hashLen → (Reg → BitVec 32) → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pred P := fun _ _ _ _ => True

/-- Two runs with the layout and saved registers of `e`, that stop at the
same candidate, each satisfying `Ctx` and `Φ`. -/
def TwoAt (P : RfcHash) (Φ : Pred P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pred P) (a b : State) : Prop := ∃ e, TwoAt P Φ e a b

variable {P : RfcHash}

theorem two_exists {Φ : Pred P} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ e, RelCT isa (TwoAt P Φ e) c Q) : RelCT isa (Two P Φ) c Q :=
  VG.RelCT.exists_ h

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g m₀ t, Φ L g m₀ t → Ψ L g m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ _ f₁, h _ _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL hq c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL hq c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem sp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- The registers that hold the pointers agree. -/
theorem ptr_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : ∀ r ∈ ptrRegs, t₁.gpr r = t₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r4, c₂.r4]
  · rw [c₁.r5, c₂.r5]
  · rw [c₁.r6, c₂.r6]
  · rw [c₁.r8, c₂.r8]
  · rw [c₁.r11, c₂.r11]

/-- A block whose addresses depend only on the registers that hold pointers. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr ptrRegs) (fun _ _ ⟨_, _, _, _, c₁, c₂, _, _⟩ => agree_regs (ptr_two c₁ c₂)) h

/-- Code whose addresses depend only on the registers `rs`, which agree. -/
theorem two_tr {c : Prog isa} {Φ : Pred P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) g₁ g₂ m₁ m₂ (t₁ t₂ : State), Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true) : RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (tA L.tab (4 * j)) 32 = t.syms n ∧
      ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.F.hiN P.F.hiC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.F.H.updN P.F.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.F.hfN P.F.hfC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `lr` changing keeps. -/
def LR (Φ : Pred P) : Prop :=
  ∀ L g m₀ (t u : State), Φ L g m₀ t → (∀ r, r ≠ .lr → u.gpr r = t.gpr r) → Φ L g m₀ u

theorem tload_taint (j : Nat) (hj : j < 3) : TaintOk [.ldr .lr .r6 (4 * j)] := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_ct {Φ : Pred P} {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k : Nat} (hn : TabFn P j n c ts) (hΦ : LR Φ)
    (hcall : RelCT isa (Two P Φ) (.frame (.push rs) (.call n c) (.pop r k)) fun _ _ => True) :
    RelCT isa (Two P Φ) (Cfg.tcall j ts rs r k) fun _ _ => True := by
  unfold Cfg.tcall
  refine (two_wp (Ψ := fun L g m₀ u => Φ L g m₀ u ∧ u.gpr .lr = L.fa n ∧ u.syms n = L.fa n ∧
      ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c))
    (two_blk (tload_taint j hj)) fun L g m₀ t hL hk hc hφ => ?_).seq ?_
  · obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
    exact WP.mono_syms (Q := fun u' => Ctx L g m₀ u' ∧ u'.gpr .lr = m₀.readW (tA L.tab (4 * j)) 32 ∧
        ∀ q, q ≠ .lr → u'.gpr q = t.gpr q)
      (tabLd_ok hL hc (d := .lr) (by decide) (o := 4 * j) (by omega_using [hj]) fun u' c' _ v' k' =>
        WP.block_nil ⟨c', v', k'⟩) fun u' ⟨c', v', k'⟩ sy =>
      ⟨c', hΦ _ _ _ _ _ hφ k', by rw [v', hw, hfa], by rw [sy, hfa], by rw [sy]; exact hf⟩
  · cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      refine RelCT.frame_icalls_of_call (hcall.mono (fun _ _ => Two.mono fun _ _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
      · show addrs (.push rs) s₁ = addrs (.push rs) s₂
        simp only [addrs, sp_two c₁ c₂]
      · obtain ⟨g₁, y₁⟩ := push_some_gpr hp₁
        obtain ⟨g₂, y₂⟩ := push_some_gpr hp₂
        refine ⟨(e.1.fa n).setWidth 64, by show some ((u₁.gpr .lr).setWidth 64) = _; rw [g₁, f₁.2.1],
          by show some ((u₂.gpr .lr).setWidth 64) = _; rw [g₂, f₂.2.1], ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => (u₁.syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [y₁, ← f₁.2.2.1]; exact f₁.2.2.2
        · show (q :: ts).find? (fun p => (u₂.syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [y₂, ← f₂.2.2.1]; exact f₂.2.2.2

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

/-- The arguments of the streaming `update`, for `cnt` bytes held and the
data at `dv L` of `len` bytes. -/
def UA (P : RfcHash) (cnt : Nat) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = dv L ∧ u.gpr .r2 = BitVec.ofNat 32 cnt ∧
    u.gpr .r3 = 0 ∧ u.gpr .r7 = BitVec.ofNat 32 len ∧ u.gpr .r10 = L.scr + BitVec.ofNat 32 384

/-- The arguments of HMAC's `finalize`, for `cnt` bytes held and the MAC to `dst`. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = BitVec.ofNat 32 cnt ∧ u.gpr .r3 = 0 ∧ u.gpr .r10 = L.fp + BitVec.ofNat 32 dst ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

theorem lr_ia : LR (IA P) := fun _ _ _ _ _ ⟨a, b, c, d, e⟩ hr => ⟨(hr _ (by decide)).trans a,
  (hr _ (by decide)).trans b, (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e⟩

theorem lr_ua {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} : LR (UA P cnt dv len) :=
  fun _ _ _ _ _ ⟨a, b, c, d, e, f⟩ hr => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e, (hr _ (by decide)).trans f⟩

theorem lr_fa {cnt dst : Nat} : LR (FA P cnt dst) :=
  fun _ _ _ _ _ ⟨a, b, c, d, e, f⟩ hr => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e, (hr _ (by decide)).trans f⟩

theorem hinit_ct :
    RelCT isa (Two P (IA P)) (.frame (.push [.r12, .lr]) (.call P.F.hiN P.F.hiC) (.pop .r12 8))
      fun _ _ => True :=
  two_exists fun e => hi_rel P.ok.hi (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.sp, c₂.sp⟩

theorem hupd_ct {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P cnt dv len))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call P.F.H.updN P.F.H.updC) (.pop .r1 16)) fun _ _ => True :=
  two_exists fun e => Proof.Pbkdf2.Whole.Arm.upd_rel P.ok.hH (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [Pbkdf2.Stream.Arm.count, Pbkdf2.Stream.Arm.count, a₁.2.2.1, a₁.2.2.2.1, a₂.2.2.1, a₂.2.2.2.1],
      c₁.sp, c₂.sp⟩

theorem hfin_ct {cnt dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    RelCT isa (Two P (FA P cnt dst))
      (.frame (.push [.r10, .r12]) (.call P.F.hfN P.F.hfC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => hf_rel P.ok.hf (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [a₁.2.2.1, a₂.2.2.1], by rw [a₁.2.2.2.1, a₂.2.2.2.1], c₁.sp, c₂.sp⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk Cfg.initArgs := ⟨_, by taint_decide⟩
theorem updVArgs_taint : TaintOk Cfg.updVArgs := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).initK fun _ _ => True :=
  (two_wp (Ψ := IA P) (two_blk initArgs_taint) fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2.2.1 hc) fun _ ⟨c, _, a, b, d, e, f, _⟩ => ⟨c, a, b, d, e, f⟩).seq
    (tcall_ct (by decide) tfn_init lr_ia hinit_ct)

/-- The inner state updated with `V`. -/
theorem updV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).updV fun _ _ => True := by
  unfold Cfg.updV
  refine (two_wp (Ψ := UA P P.F.H.B (fun L => L.fp + BitVec.ofNat 32 fV) P.F.H.D) (two_blk updVArgs_taint)
    fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_upd lr_ua (hupd_ct (fun _ _ => .inl ⟨64, rfl, by anums⟩) (by anums)))
  simp only [Cfg.updVArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine fpAdd_ok c₁ (d := .r1) (by decide) (o := fV) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine ldD_ok hL c₄ (d := .r7) (by decide) fun t₅ c₅ _ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₅ (d := .r10) (by decide) (o := sWork) (by decide) fun t₆ c₆ _ v₆ k₆ => ?_
  refine WP.block_nil ⟨c₆, ?_, ?_, ?_, ?_, ?_, v₆⟩
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide)]
    exact v₁
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃, hk.2.2.1.1]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide)]; exact v₄
  · rw [k₆ _ (by decide) (by decide), v₅, hk.2.2.1.1]

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) (ht : TaintOk (Cfg.updMArgs len)) :
    RelCT isa (Two P Φ) ((cfgOf P).updM len) fun _ _ => True := by
  unfold Cfg.updM
  refine (two_wp (Ψ := UA P (P.F.H.B + P.F.H.D) (fun L => L.scr + BitVec.ofNat 32 sMsg) len) (two_blk ht)
    fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_upd lr_ua
      (hupd_ct (fun _ _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega_using [], by simp only [sMsg]; omega_using [hlen]⟩) hlen))
  simp only [Cfg.updMArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sMsg) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide)
  refine mov0_ok c₅ (d := .r3) (by decide) fun t₆ c₆ _ v₆ k₆ => ?_
  refine movw_ok c₆ (d := .r7) (v := len) (by decide) (by omega_using [hlen]) fun t₇ c₇ _ v₇ k₇ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₇ (d := .r10) (by decide) (o := sWork) (by decide) fun t₈ c₈ _ v₈ k₈ => ?_
  refine WP.block_nil ⟨c₈, ?_, ?_, ?_, ?_, ?_, v₈⟩
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]; exact v₁
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hk.2.2.1.1, BitVec.ofNat_add]
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide)]; exact v₆
  · rw [k₈ _ (by decide) (by decide)]; exact v₇

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_ct {Φ : Pred P} {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (he : encodable (BitVec.ofNat 32 dst) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (ht : TaintOk (Cfg.finArgs len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).fin len dst) fun _ _ => True := by
  unfold Cfg.fin
  refine (two_wp (Ψ := FA P (P.F.H.B + P.F.H.D + len) dst) (two_blk ht) fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_fin lr_fa (hfin_ct hdst))
  simp only [Cfg.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide)
  refine wp_dpS (op2_imm hle) fun t₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide)
  refine mov0_ok c₆ (d := .r3) (by decide) fun t₇ c₇ _ v₇ k₇ => ?_
  refine fpAdd_ok c₇ (d := .r10) (by decide) he fun t₈ c₈ _ v₈ k₈ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₈ (d := .r12) (by decide) (o := sWork) (by decide) fun t₉ c₉ _ v₉ k₉ => ?_
  refine WP.block_nil ⟨c₉, ?_, ?_, ?_, ?_, ?_, v₉⟩
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]; exact v₁
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.gpr, dpVal, u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hk.2.2.1.1, BitVec.ofNat_add, BitVec.ofNat_add]
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide)]; exact v₇
  · rw [k₉ _ (by decide) (by decide)]; exact v₈

/-! ## HMAC -/

/-- HMAC's states, with `n` bytes of text after the key. -/
def Sx (P : RfcHash) (n : Nat) : Pred P := fun L g m₀ u =>
  ∃ t text, St P L g m₀ t text u ∧ text.length = n

theorem initS_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).initK (Two P (Sx P 0)) :=
  two_wp initK_ct fun _ _ _ t hL hk hc _ =>
    WP.mono (init_step hL hk.2.2.1 hc) fun _ h => ⟨h.ctx, t, [], h, rfl⟩

theorem updVS_ct : RelCT isa (Two P (Sx P 0)) (cfgOf P).updV (Two P (Sx P P.F.H.D)) :=
  two_wp updV_ct fun _ _ _ _ hL hk _ ⟨t, text, hs, hl⟩ => by
    rw [List.eq_nil_of_length_eq_zero hl] at hs
    exact WP.mono (updV_step hL hk.2.2.1 hs) fun _ h => ⟨h.ctx, t, _, h, length_bytesAt _ _ _⟩

theorem updMS_ct {len : Nat} (hlen : len ≤ 256) (ht : TaintOk (Cfg.updMArgs len)) :
    RelCT isa (Two P (Sx P P.F.H.D)) ((cfgOf P).updM len) (Two P (Sx P (P.F.H.D + len))) :=
  two_wp (updM_ct hlen ht) fun _ _ _ _ hL hk _ ⟨t, text, hs, hl⟩ =>
    WP.mono (updM_step hL hk.2.2.1 hs hl hlen) fun _ h => ⟨h.ctx, t, _, h, by
      rw [List.length_append, hl, length_bytesAt]⟩

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  initS_ct.seq (updVS_ct.seq (fin_ct (by simp only [fV]; anums) (by decide) (by decide) ⟨_, by taint_decide⟩))

/-- `K = HMAC_K(V ‖ m)`, for the message of `len` bytes at `scratch + sMsg`. -/
theorem hmacK_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) (hle : encodable (BitVec.ofNat 32 len) = true)
    (t₂ : TaintOk (Cfg.updMArgs len)) (t₃ : TaintOk (Cfg.finArgs len fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmacK len) fun _ _ => True :=
  initS_ct.seq (updVS_ct.seq ((updMS_ct hlen t₂).seq (fin_ct (by simp only [fK]; anums) (by decide) hle t₃)))

/-- `K = HMAC_K(V ‖ b (‖ d ‖ h))`, then `V = HMAC_K(V)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} (hb : b < 2) (full : Bool) {len : Nat}
    (hlen : len = if full then 1 + 2 * P.Q else 1) (t₁ : TaintOk ((cfgOf P).msg b full))
    (t₂ : TaintOk (Cfg.updMArgs len)) (t₃ : TaintOk (Cfg.finArgs len fK)) :
    RelCT isa (Two P Φ) (.seq (.block ((cfgOf P).msg b full)) (.seq ((cfgOf P).hmacK len) (cfgOf P).hmacV))
      fun _ _ => True := by
  have hl : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  have he : encodable (BitVec.ofNat 32 len) = true := encodable_lt (by
    cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums)
  refine (two_wp (Ψ := Tt P) (two_blk t₁) fun _ _ _ _ hL hk hc _ =>
    WP.mono (msg_ok hL (by rw [hk.1]) hc hb full) fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := Tt P) (hmacK_ct hl he t₂ t₃) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok hL hk.2.2.1 hc hl he) fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_using [hb]
  · exact rekey_gen_ct hb true (len := 1 + 2 * (cfgOf P).len) rfl (by exact (rT P).msgF₀) (by exact (rT P).updM)
      (by exact (rT P).finM)
  · exact rekey_gen_ct hb true (len := 1 + 2 * (cfgOf P).len) rfl (by exact (rT P).msgF₁) (by exact (rT P).updM)
      (by exact (rT P).finM)

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (by decide) false (len := 1) rfl (by exact (rT P).msgN) ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩

/-! ## The byte loops -/

/-- A byte copy's registers: `n` bytes from `q L` to `p L`. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen → BitVec 32) (n : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r1 = q L ∧ u.gpr .r2 = p L ∧ u.gpr .r3 = BitVec.ofNat 32 n

theorem copyLoop_taint : ∃ hc, (VG.Taint.check taint (τr [.r1, .r2, .r3]) copyLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pred P} {p q : Lay P.I.hashLen → BitVec 32} {n : Nat}
    (h : ∀ L g m₀ u, Φ L g m₀ u → CpA P p q n L g m₀ u) :
    RelCT isa (Two P Φ) copyLoop fun _ _ => True :=
  two_tr [.r1, .r2, .r3] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := h _ _ _ _ f₁; obtain ⟨a₂, b₂, c₂⟩ := h _ _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm) copyLoop_taint

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pred P := fun L g m₀ u => ∃ t₀ K V₀, CI P L g m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pred P := fun L _ _ u => tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pred P := fun L g m₀ u =>
  CpA P (fun L => L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D)) (fun L => L.fp + BitVec.ofNat 32 fV) P.F.H.D
    L g m₀ u ∧ TL P j L g m₀ u

theorem keepArgs_taint : TaintOk Cfg.keepArgs := ⟨_, by taint_decide⟩

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : j < P.nV) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  obtain ⟨-, hND, -⟩ := nV_facts P
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.F.H.D)) (by omega_using [hND, hD64, hQ66])
  have hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  have : fT = 328 := rfl; have : fV = 64 := rfl; have : fTlen = 464 := rfl
  refine (two_wp (Ψ := TL P j) hmacV_ct fun L g m₀ t hL hk hc hJ => ?_).seq
    ((two_wp (Ψ := KA P j) (two_blk keepArgs_taint) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.2.2.1 hc hl) fun u ⟨c, hm, h1, h2, h3, _⟩ =>
        ⟨c, ⟨h1, h2, h3⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := Tt P) (cp_ct fun _ _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨h1, h2, h3⟩, _⟩ => ?_).seq
      (two_blk (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, hI⟩ := hJ
    have hbf := hL.B_fit
    refine WP.mono (hmacV_ok hL hk.2.2.1 hc) fun u ⟨hc₁, _, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  · have hbf := hL.B_fit
    have hpa : State.addr (L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D)) =
        L.B + BitVec.ofNat 64 (352 + j * P.F.H.D) := by
      rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
    have hqa : State.addr (L.fp + BitVec.ofNat 32 fV) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
    exact WP.mono (cp_ok hL hc (p := L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D))
      (q := L.fp + BitVec.ofNat 32 fV) (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [hqa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa, hqa]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)))
      fun _ h => ⟨h.1, trivial⟩

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep .ne) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨_, _, _, _, _, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, _, hQ66, _, _⟩ := P.wsizes
  have h := VG.RelCT.loop (M := isa) (c := .ne) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV)
    (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega_using [hN1, hn0]
      have hb : (P.nV - n + 1) * P.F.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega_using [hN1, hn0]) (Nat.le_refl P.F.H.D)) (by omega_arith)
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L g m₀ u => CJ P (P.nV - n + 1) L g m₀ u ∧
          isa.eval .ne u = some (decide ((P.nV - n + 1) * P.F.H.D < P.Q))) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.2.2.1 hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx, ⟨t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        rw [f₁.2, f₂.2]
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have : ¬ (P.nV - n + 1) * P.F.H.D < P.Q := by
          intro h'; have := f₁.2; rw [decide_eq_true h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hNn : P.nV - n + 1 = P.nV := by
          have : ¬ P.nV - n + 1 < P.nV := fun h => this ((nV_lt P _).mp h)
          omega_using [hN1, hn0, this]
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have h' : (P.nV - n + 1) * P.F.H.D < P.Q := by
          by_contra h'; have := f₁.2; rw [decide_eq_false h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hlt := (nV_lt P (P.nV - n)).mpr h'
        refine ⟨n - 1, by omega_using [hn0], by omega_using [hlt], by omega_using [hnN], e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega_using [hn0, hnN]]
        · exact f₁.1
        · exact f₂.1)
  exact h.mono (fun s₁ s₂ hp => ⟨hN1, Nat.le_refl _, by rwa [Nat.sub_self]⟩) fun _ _ h => h

theorem candTop_ct {Φ : Pred P} : RelCT isa (Two P Φ) (.block (cfgOf P).candTop) fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = (cfgOf P).conv fT (cfgOf P).sh by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact two_blk (by exact (rT P).convT hb)

theorem tInit_taint : TaintOk Cfg.tInit := ⟨_, by taint_decide⟩

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk tInit_taint) fun L g m₀ t hL hk hc _ =>
    WP.mono (tInit_ci hL hc) fun u hI => ⟨hI.ctx, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

/-! ## One candidate -/

/-- `core`, in its frame, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
      (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => frame2_rel rfl P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun s₁ s₂ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      have h₁ := c₁.sp24 hL
      have h₂ := c₂.sp24 hL
      refine ⟨sp_two c₁ c₂, core_pre hL hk c₁ a₁, core_pre hL hk c₂ a₂, ?_,
        core_cov hL hk c₁, core_covW hk.1 c₁, core_cov hL hk c₂, core_covW hk.1 c₂⟩
      simp only [coreK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        Pbkdf2.Stream.Arm.ce0, Pbkdf2.Stream.Arm.ce1, Pbkdf2.Stream.Arm.ce2, Pbkdf2.Stream.Arm.ce3, pushed_gpr,
        pushed_sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₁) (by omega_arith),
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₂) (by omega_arith), a₁.r12, a₂.r12, sp_two c₁ c₂, true_and]
      intro c hc
      have hmem : c ∈ e.1.cs := hk.2.1 ▸ hc
      rw [core_syms c₁ hmem, core_syms c₂ hmem]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem goOn_blk : TaintOk Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk Cfg.stop := ⟨_, by taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u) (two_blk (by exact (rT P).coreArgs))
    fun _ _ _ _ _ _ hc hi => try₂_ok hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
    fun _ _ _ _ hL _ hc hi => try₄_ok hL hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := Tt P) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL hk.2.2.1 (by rw [hk.1]) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → Two P (fun L _ m₀ t => Exit P L m₀ i t) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (fun L _ m₀ t => LoopInv P L m₀ (i + 1) t) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega_using []), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega_using [hj])), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {T n : Nat} (h : T - n + 1 < T) : T - (T - n + 1) < n ∧ T - (T - (T - n + 1)) = T - n + 1 :=
  ⟨by omega_using [h], by omega_using [h]⟩

theorem tries_ct :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

theorem initCnt_blk₀ : TaintOk [.movw .r9 (BitVec.ofNat 16 8)] := ⟨_, by taint_decide⟩

/-- The count's initial `movw`, for any count: the analysis does not read its
immediate (`Taint.check_eraseOff`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk c.initCnt := by
  obtain ⟨h, hs⟩ := initCnt_blk₀
  have hb : Taint.NoBase (τr ptrRegs) := ⟨rfl, rfl⟩
  have e := Taint.check_eraseOff (.block c.initCnt) h hb
  have e₀ := Taint.check_eraseOff (.block [.movw .r9 (BitVec.ofNat 16 8)]) h hb
  have he : Code.eraseOff (.block c.initCnt) = Code.eraseOff (.block [.movw .r9 (BitVec.ofNat 16 8)]) := rfl
  exact ⟨h, e ▸ he ▸ e₀ ▸ hs⟩

theorem wipe_taint : ∃ hc, (VG.Taint.check taint (τr ptrRegs) Cfg.wipe hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (fun L _ m₀ t => QX P L m₀ t)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) (fun L => L.dg)
      (min P.F.H.D P.Q)) (two_blk (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.2.2.1 hc) fun _ ⟨c, _, _, h3, h2, h1⟩ => ⟨c, h1, h2, h3⟩).seq
    (cp_ct fun _ _ _ _ h => h)

/-- The arguments of the copy of `core`'s digest, if `big`. -/
theorem xcArgs_ok {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) (hT : TabL P L)
    (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧ u.gpr .r1 = L.dg ∧
      u.gpr .r2 = L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D) ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D := by
  obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hW
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have : fXc = 260 := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fXc) (by decide)) fun u₁ ⟨c₁, _, _, _⟩ => ?_
  refine ldD_ok hL c₁ (d := .r3) (by decide) fun u₂ c₂ _ v₂ _ => ?_
  rw [hT.1] at v₂
  refine WP.mono (dstArgs_ok hL c₂ (a := fXc + (cfgOf P).len - 1) (n := P.F.H.D) (by simp only [cfgOf_len]; anums)
    (by simp only [cfgOf_len]; omega_arith) v₂) fun u₃ ⟨c₃, _, h2, h1, h3, _⟩ => ?_
  rw [cfgOf_len] at h2
  exact ⟨c₃, h1, h2, h3⟩

theorem prepH_ct : RelCT isa (Two P (fun L _ m₀ t => QX P L m₀ t)) (cfgOf P).prepH
    (Two P (fun L _ m₀ t => QA P L m₀ t)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hb
    obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
    refine (two_wp (Ψ := CpA P (fun L => L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (fun L => L.dg) P.F.H.D)
      (two_blk (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
        WP.mono (xcArgs_ok hL hk.2.2.1 hb hc) fun _ ⟨c, h1, h2, h3⟩ => ⟨c, h1, h2, h3⟩).seq ?_
    refine (two_wp (Ψ := Tt P) (cp_ct fun _ _ _ _ h => h) fun L g m₀ t hL hk hc ⟨h1, h2, h3⟩ => ?_).seq
      (two_blk (by exact (rT P).convC hb))
    have hbf := hL.B_fit
    have ng := hL.ng
    have hdn : P.F.H.D ≤ P.I.hashLen := hk.2.2.2
    have : fXc = 260 := rfl
    have hpa : State.addr (L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) =
        L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D)) := by
      rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
    exact WP.mono (cp_ok hL hc (p := L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (q := L.dg)
      (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ hdn⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 284 + (P.Q - 1 - P.F.H.D)) (n := P.F.H.D)
        (by omega_arith)).symm.sub_left (Region.sub_prefix hdn))) fun _ h => ⟨h.1, trivial⟩

/-- The body after the prologue. -/
theorem body_ct :
    RelCT isa (Two P (Tt P)) (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV)
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne .ne) Cfg.wipe))))))) fun _ _ => True := by
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := fun L _ m₀ t => QB P L m₀ t) (two_blk (by exact (rT P).initKV))
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by decide))
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by decide))
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk (initCnt_blk _))
    fun _ _ _ _ _ _ hc h => stageE_ok (P := P) hc h).seq ?_
  exact tries_ct.seq (two_tr ptrRegs (fun _ _ _ _ _ _ _ c₁ c₂ _ _ => ptr_two c₁ c₂) wipe_taint)

/-! ## The prologue -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂) ∧
    a = allocated frameBytes s₁ ∧ b = allocated frameBytes s₂

theorem prologue_tail : ∃ hc, (VG.Taint.check taint (τr [.r12])
    (.block (Impl.Ecdsa.Rfc6979.Arm.saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .str .r2 .r12 fDigest, .ldr .r11 .r12 frameBytes,
        .ldr .r6 .r12 (frameBytes + 4), .mov .r8 (.reg .r12)] : List Instr)))
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- The prologue reads `sp`, which agrees, and then addresses the frame through `r12`. -/
theorem start_blk {ns : List String} : RelCT isa (Entered P ns) (.block Cfg.prologue) fun _ _ => True := by
  rw [Cfg.prologue, List.cons_append]
  refine block_cons_ct (R := fun a b => ∀ r ∈ [Reg.r12], a.gpr r = b.gpr r)
    (fun a b a' b' ⟨s₁, s₂, ⟨_, _, hsp, _⟩, ea, eb⟩ ha hb => ?_) ?_
  · subst ea eb
    simp only [reduceExec, show (0 : Nat) < 256 by decide, ↓reduceIte, Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    simp only [State.setReg, ↓reduceIte, allocated, hsp]
  · let ⟨_, h⟩ := prologue_tail
    exact VG.RelCT.taint (A := taint) _ (fun _ _ h => agree_regs h) h

/-- After the prologue, the runs are related by `Two`, with the layout of the
arguments, which agree, and the same number of candidates. -/
theorem start_ct {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.prologue) (Two P (Tt P)) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨p₁, p₂, hsp, h0, h1, h2, ha0, ha1, hres, hsy, hns'⟩, rfl, rfl⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok (P := P) p₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok (P := P) p₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have eqSy : (fun n => if n ∈ P.R.coreConsts.map Prod.fst then s₂.syms n else 0) =
      (fun n => if n ∈ P.R.coreConsts.map Prod.fst then s₁.syms n else 0) := by
    funext n
    by_cases hn : n ∈ P.R.coreConsts.map Prod.fst
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      simp only [hn, ↓reduceIte]
      exact (hsy c hc).symm
    · simp only [hn, ↓reduceIte]
  have eqFa : (fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₂.syms n else 0) =
      (fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₁.syms n else 0) := by
    funext n
    by_cases hn : n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN]
    · simp only [hn, ↓reduceIte]
      exact (hns' n (hns n hn)).symm
    · simp only [hn, ↓reduceIte]
  have hl : layOf P s₂ = layOf P s₁ := by
    simp only [layOf, lay, hsp, h0, h1, h2, ha0, ha1, eqSy, eqFa]
  have hr : (result P.I s₁.mem (State.addr (layOf P s₁).d) (State.addr (layOf P s₁).dg)).2 =
      (result P.I s₂.mem (State.addr (layOf P s₁).d) (State.addr (layOf P s₁).dg)).2 := by
    show (result P.I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result P.I s₂.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2
    rw [hres, h1, h2]
  rw [hl] at y₂
  exact ⟨ht, ⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, y₁, y₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (R := fun _ _ => True) ?_)
  rw [Cfg.body]
  exact ((start_ct hns).seq body_ct).mono (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-!
# Deterministic ECDSA on 32-bit ARM: the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCodeT`) runs the one body (`cfgT`, the same
for every hash function), which reads `D` and `B`, the digest length and
HMAC's block size, from the table `hmac` (its words 4 and 5) and calls the
table's functions. For the hash functions `vs` whose tables it takes, of
sizes the frame holds (`OK`: their functions of the same name have the same
code, and each is of one of the hash functions with HMAC on ARMv7, `WOk`),
the table of each `w` makes the body the code for `w`'s hash function
(`hashOf`, with `cfgT_eq`, which holds by `rfl`), which meets the contract
with that hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that
contract for whichever of the tables `hmac` holds, on entry;
`TableSpec.lean` shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.HmacTable.Arm (HVar vars tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf tA)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  big := R.big
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := (cfgT R tries vs).sign

/-! ## The hash functions -/

/-- What the code needs of a hash function `w`: digest length and block
size of one of the hash functions the frame holds, states and working
space no larger than SHA-512's, and digests of `D` bytes. -/
structure WOk (w : HVar) : Prop where
  db : (w.F.H.D, w.F.H.B) ∈ shapes
  hS : w.F.H.S ≤ 192
  hWi : w.ok.Wi * 8 ≤ 1872
  hWf : w.ok.Wf * 8 ≤ 1872
  hWb : w.ok.hH.Wb ≤ 1872
  macLen : ∀ x, (w.ok.hH.SH.H.hash x).length = w.F.H.D

/-- What the proof needs of the hash functions whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ ∀ w ∈ vs, WOk w

theorem sha512_len (iv : Spec.Sha512.HashValue) (n : Nat) (hn : n ≤ 64) (x : List Byte) :
    ((Spec.Sha512.finalHash iv x).take n).length = n := by
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; omega_using [hn]

/-- Which of `vars` have a function's name in common: none HMAC's `init` or `finalize`, and
`update` only SHA-224 with SHA-256 and the four of SHA-512. One evaluation, in which the kernel
reads each name once. -/
private theorem vars_names : ∀ (i : Nat) (hi : i < 8) (j : Nat) (hj : j < 8),
    ((vars[i]'hi).F.hiN = (vars[j]'hj).F.hiN → i = j) ∧
    ((vars[i]'hi).F.H.updN = (vars[j]'hj).F.H.updN →
      i = j ∨ (2 ≤ i ∧ i < 4 ∧ 2 ≤ j ∧ j < 4) ∨ (4 ≤ i ∧ 4 ≤ j)) ∧
    ((vars[i]'hi).F.hfN = (vars[j]'hj).F.hfN → i = j) := by
  decide +kernel

/-- Every hash function with HMAC on ARMv7 meets `WOk`. -/
theorem vars_coh : Coh vars := by
  intro w hw w' hw'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw'
  obtain ⟨n₁, n₂, n₃⟩ := vars_names i hi j hj
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain rfl := n₁ h; rfl
  · rcases n₂ h with rfl | ⟨a, b, c, d⟩ | ⟨a, b⟩
    · rfl
    · obtain rfl | rfl : i = 2 ∨ i = 3 := by omega
      all_goals obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
      all_goals rfl
    · have hi' : i < 8 := hi
      have hj' : j < 8 := hj
      obtain rfl | rfl | rfl | rfl : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      all_goals obtain rfl | rfl | rfl | rfl : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      all_goals rfl
  · obtain rfl := n₃ h; rfl

theorem vars_ok : OK vars := by
  refine ⟨vars_coh, fun w hw => ?_⟩
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Md5.hash x).length = 16
        rw [Proof.Md5.hash_eq]; exact Proof.Md5.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha1.hash x).length = 20
        rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha256.sha224 x).length = 28
        simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap,
          List.map_const']⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha256.hash x).length = 32
        rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
        exact sha512_len _ 48 (by decide) x⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
        exact Proof.Hmac.Generic.Common.finalHash_length _ _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_224 x).take 28).length = 28
        exact sha512_len _ 28 (by decide) x⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_256 x).take 32).length = 32
        exact sha512_len _ 32 (by decide) x⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Proof.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.hH.SH.H
  hashLen := w.F.H.D
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 16

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    (w : HVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  F := w.F
  ok := w.ok
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  macLen := hw.macLen
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.db
  hS := hw.hS
  hWi := hw.hWi
  hWf := hw.hWf
  hWb := hw.hWb

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.ok.hH.SH.H m d dg := by
  simp only [Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.glen]

/-! ## The contract on entry -/

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.F (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (tA (stackArg s 1) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.G w.ok.hH.SH.H s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.F (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length :=
  (List.getElem?_eq_some_iff.mp w.idx).1

/-- Two hash functions whose tables have the same index are the same. -/
theorem same_hash {w w' : HVar}
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.G) = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.ok.hH.SH.H = w.ok.hH.SH.H := by
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have h₁ := index_lt w; have h₂ := index_lt w'
    have hl : Spec.Mgf1.hashes.length < 2 ^ 32 := by decide
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h₂, hl]), Nat.mod_eq_of_lt (by omega_using [h₁, hl])] at this
    exact this
  have hG : w'.G = w.G := by
    have h₁ := w.idx; have h₂ := w'.idx
    rw [e, h₁] at h₂
    exact (Option.some.inj h₂).symm
  refine ⟨hG, ?_⟩
  have h₁ := w.hmac; have h₂ := w'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (ns := names vs) hp.1) fun s' ⟨hpr, hpost⟩ => ⟨hpr, ?_⟩
  intro w' _ hw' hp'
  obtain ⟨hG, hH⟩ := same_hash (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
        (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
        (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT at e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [(hashOf hC vs w hw).F.hiN, (hashOf hC vs w hw).F.H.updN, (hashOf hC vs w hw).F.hfN],
      n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact sign_ct (P := hashOf hC vs w hw) hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

end VG.Proof.Ecdsa.Rfc6979.Arm
