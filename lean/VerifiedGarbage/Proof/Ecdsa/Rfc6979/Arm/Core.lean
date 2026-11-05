module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Cand
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

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
  have he : encodable (BitVec.ofNat 32 (cfgOf P).fDg) = true := by
    simp only [Cfg.fDg]; split <;> decide
  simp only [Cfg.coreArgs]
  refine movr_ok hc (d := .r0) (r := .r4) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine movr_ok c₁ (d := .r1) (r := .r5) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  have h0 : t₂.gpr .r0 = L.out := by rw [k₂ _ (by decide), v₁, hc.r4]
  have h1 : t₂.gpr .r1 = L.d := by rw [v₂, c₁.r5]
  have h9 : t₂.gpr .r9 = t.gpr .r9 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  have m : t₂.mem = t.mem := by rw [m₂, m₁]
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
  have hf := fDg_le P
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
  have hcs : c∈L.cs := hk.2.1 ▸ hcc
  have table : (⟨State.addr (L.sy c.1),8*c.2.length⟩ : Region)∈L.TBLs := List.mem_map_of_mem
    (f := fun c => (⟨State.addr (L.sy c.1),8*c.2.length⟩ : Region)) hcs
  have ht := hL.tables _ table
  have fit : 8*c.2.length≤2^64 := by dsimp only at ht; omega
  have hpushed : Frame [L.STK] t.mem (pushed [.r12,.lr] t).mem := by
    apply (pushed_frameA (rs := [.r12,.lr]) (s := t) (by change 8≤t.sp.toNat; have := hc.sp24 hL; omega_arith)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨L.STK,by simp,?_⟩
    have ea : belowA t.sp 8=⟨L.B+BitVec.ofNat 64 16,8⟩ := by
      change (⟨State.addr (t.sp-BitVec.ofNat 32 8),8⟩ : Region)=_
      rw [core_sp hL hc]
    change Region.Sub (belowA t.sp 8) L.STK
    rw [ea]
    exact Offset.sub_base _ (by omega_arith)
  have frame := hc.frame.trans (hpushed.sub fun r hr => by
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
  have h24 := hc.sp24 hL
  have hsp := core_sp hL hc
  have := hL.nB; have := L.sp.isLt
  have hq : L.q = P.R.E.C.len := hk.1
  have eD : (⟨State.addr L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  have eO : (⟨State.addr L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
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
    have eqW : coreWr P L=[L.OUT,L.SCR] := by simp only [coreWr,Lay.OUT,hk.1]
    rw [eqW] at tab
    exact tab

theorem core_cov (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) := by
  have hq : L.q = P.Q := hk.1
  have hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
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
  have h24 := hc.sp24 hL
  have hst := hc.stk_eq hL
  have hq : L.q = P.Q := hk.1
  have eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine frame2_ok (ra := .r12) (rb := .lr) (t := .r12) rfl (by decide) P.R.coreX
    (by show armStack P.R.coreC ≤ 16; rw [P.R.coreStack]; omega_arith) h24 (core_pre hL hk hc hr)
    (core_cov hL hk hc) (core_covW hq hc) fun s₂ ha hpost syEnd => ?_
  rw [eW] at ha
  have hf : Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem (popped .r12 8 s₂).mem := ha.frame.sub fun q hq' => by
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
    have hQl : P.Q ≤ 72 := by have := P.wsizes.2.2.2.2.2.1; omega_arith
    have hq : L.q = P.Q := hk.1
    have hs : coreSigOf P.R.E (pushed [.r12, .lr] t).mem (State.addr L.d) (dgAddr P L) (kArg L) =
        coreSig P L t.mem := by
      have d1 : (stk t).Disjoint ⟨State.addr L.d, P.R.E.C.len⟩ := by
        rw [hst]
        exact (hL.kd.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
      have d2 : (stk t).Disjoint ⟨dgAddr P L, P.R.E.C.len⟩ := by rw [hst]; exact gB.symm
      have d3 : (stk t).Disjoint ⟨kArg L, P.R.E.C.len⟩ := by rw [hst]; exact kB.symm
      simp only [coreSigOf, coreSig, Rfc6979.ecdsa_bytesAt]
      rw [p2_bytes h24 d1 (by omega_arith), p2_bytes h24 d2 (by omega_arith), p2_bytes h24 d3 (by omega_arith)]
    simp only [coreK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0,
      ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1, hr.r2, hr.r3, dgArg_w hL, kArg_w hL, hs] at hpost
    rw [popped_gpr (by decide), popped_gpr (by decide), popped_mem]
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.Arm
