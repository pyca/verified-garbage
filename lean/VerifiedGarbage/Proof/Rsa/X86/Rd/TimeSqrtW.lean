module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWStep
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWNorm
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFix
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFin
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFirst
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWSub
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Base
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2

/-! # The square root's timing on i686

`RecoverDetRt.sqrt` (`Rd/SqrtW.lean` has its run): its loops count by header words (`sC4`, `sB`,
`sBc`, `sCt`), which the analysis forgets after the arrays' stores, so the straight pieces are
leaves (`leafP`), the loops related by `relWordStagesL`, `relBitStagesL`, `relTimesH` and `relLoop`.

`fixX`'s add loop counts in `edi`, so its last block starts where `edi` is not the working space:
it is checked from `τE`, which knows nothing of `edi` until `restoreEdi` reloads it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 (sc at_)
open VG.Impl.Rsa.X86.KeyRt (copy sel chain half arrPtr bytesB)
open VG.Proof.Rsa.X86.WordRt (MLen wq)
open VG.Proof.Rsa.X86.KeyRt (kw RtWs)
open VG.Proof.Rsa.X86.InvBatchRt.Time (view Pre0 τ0 argBytes Public)

/-! ## Leaves where `edi` is not the working space -/

/-- `τK ds` without `edi`: neither public nor a base. -/
def τE (ds : List Nat) : VG.X86.Taint.T :=
  { τK ds with regs := .ofList [.esp], bases := [] }

/-- Code the analysis checks from `τE ds`. -/
def OkE (ds : List Nat) (c : Prog isa) : Prop :=
  ∃ hint, (VG.Taint.check sseTaint (τE ds) c hint).isSome = true

/-- A state `edi` aside: `u` keeps all but the registers `rs` (not `esp`) of a leaf's start `s`, and
its memory outside the working space. -/
def EdiFree (g : Geo) (u : State) : Prop :=
  ∃ s rs, P0 g s ∧ Keeps rs s u ∧ .esp ∉ rs ∧ Outside g.B 0 g.Z s.mem u.mem

theorem EdiFree.onView {g : Geo} {u : State} (h : EdiFree g u) : EdiFree g.vw (view u g.B g.Z) := by
  obtain ⟨s, rs, p, K, sp, O⟩ := h
  exact ⟨view s g.B g.Z, rs, p.view, ⟨K.1, by simp only [view, State.withRegions_rd,
    K.2.1, K.2.2], rfl⟩, sp, O⟩

theorem wfE {g : Geo} {u : State} (ds : List Nat) (h : EdiFree g u) :
    VG.X86.Taint.Wf (τE ds) (view u g.B g.Z) := by
  obtain ⟨s, rs, ⟨hs, _, ps⟩, K, sp, O⟩ := h
  have hn := hs.ws.workspace.nowrap
  have hf : VG.Impl.Rsa.X86.Keys.hdr + 22 * VG.Proof.Rsa.X86.Keys.S (kw (16 * g.n + 24)) ≤ g.Z := hs.ws.fits
  rw [show VG.Impl.Rsa.X86.Keys.hdr = 160 from rfl] at hf
  have pu := ps.keep K sp O
  have wsu := hs.wsArg.keep K sp O
  have wr : (⟨g.B, g.Z⟩ : Region) ∈ u.wr := K.2.2 ▸ hs.ws.workspace.wr
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨List.Forall₂.cons (show 160 ≤ g.Z by omega) List.Forall₂.nil,
    List.pairwise_singleton _ _, fun r hr => by
      cases hr with
      | head => exact hn
      | tail _ h => cases h⟩, (fun p hp => by cases hp), (fun p hp => by cases hp),
    fun _ => ⟨pu.argsOk.1, fun r hr => by
      simp only [view, State.withRegions_wr, List.mem_singleton] at hr; subst r
      exact pu.argsOk.2 _ wr⟩, ?_⟩
  intro p hp
  simp only [τE, τK, τ0, List.mem_singleton] at hp
  subst p
  refine ⟨by simp only [τE, τK, τ0, VG.Proof.Rsa.X86.InvBatchRt.Time.argBytes, wid,
    VG.Impl.Rsa.X86.RecoverRt.lay]; omega, ?_⟩
  have v := wsu.value
  change u.mem.readW (addr (u.gpr .esp) (4 + 4 * wid.ws)) 32 = _ at v
  show addr (u.mem.readW (addr (u.gpr .esp) (4 + 4 * wid.ws)) 32) 0 = g.B
  rw [v]
  simp only [addr, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := g.B.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem EdiFree.pub {g : Geo} {u : State} (h : EdiFree g u) : Public wid g.args g.B g.Z g.sp u :=
  let ⟨_, _, ⟨_, _, ps⟩, K, sp, O⟩ := h
  ps.keep K sp O

/-- Two runs `edi` aside, with the header words `ds` equal, agree on `τE ds` in their views. -/
theorem agreeE {g : Geo} {s t : State} {ds : List Nat} (hds : ∀ d ∈ ds, d + 4 ≤ 160)
    (hs : EdiFree g s) (ht : EdiFree g t) (eq : ∀ d ∈ ds, w32 s.mem g.B d = w32 t.mem g.B d) :
    VG.X86.Taint.Agree (τE ds) (view s g.B g.Z) (view t g.B g.Z) := by
  have ps := hs.pub
  have pt := ht.pub
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => rfl, wfE ds hs, wfE ds ht,
    VG.X86.Taint.slotsOk_of_list rfl (fun sl hsl => ?_), ?_, fun _ => ps.stack.trans pt.stack.symm, ?_⟩
  · intro r hr
    simp only [τE, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ps.stack.trans pt.stack.symm
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hsl
    change d + 4 ≤ ([160] : List Nat).getD 0 0
    exact hds d hd
  · intro i k hk
    rw [τE, τK, VG.Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, h₁, h₂⟩ := hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hsl
    simp only at h₁ h₂
    change s.mem (g.B + BitVec.ofNat 64 k) = t.mem (g.B + BitVec.ofNat 64 k)
    have e : g.B + BitVec.ofNat 64 k = off g.B d + BitVec.ofNat 64 (k - d) := by
      simp only [off]; rw [VG.Offset.add_add]; congr 2; omega
    rw [e, Mem.readW_byte s.mem _ (show k - d < 4 by omega), Mem.readW_byte t.mem _ (show k - d < 4 by omega)]
    exact congrArg _ (BitVec.eq_of_toNat_eq (eq d hd))
  · intro k h4 hk
    change s.mem (VG.X86.Taint.argByte s (VG.X86.Taint.depth (τE ds).stk + k)) =
      t.mem (VG.X86.Taint.argByte t (VG.X86.Taint.depth (τE ds).stk + k))
    rw [show VG.X86.Taint.depth (τE ds).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq ps.argsOk.1 h4 hk, VG.X86.Taint.argByte_eq pt.argsOk.1 h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    have hi : (k - 4) / 4 < wid.ws + 2 := by
      simp only [τE, τK, τ0, VG.Proof.Rsa.X86.InvBatchRt.Time.argBytes] at hk; omega
    exact congrArg _ ((ps.arguments _ hi).value.trans (pt.arguments _ hi).value.symm)

/-- A leaf whose start is `edi` aside, checked from `τE ds`. -/
theorem leafE {g : Geo} {P Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat} (vals : Nat → Nat)
    (hds : ∀ d ∈ ds, d + 4 ≤ 160) (hpre : ∀ s, P g s → EdiFree g s)
    (hv : ∀ s, P g s → P g.vw (view s g.B g.Z))
    (hval : ∀ s, P g s → ∀ d ∈ ds, w32 s.mem g.B d = vals d)
    (hf : ∀ g' s, P g' s → WP isa c s (Q g')) (h : OkE ds c) :
    RelCT isa (Both (P g)) c (Both (Q g)) := by
  obtain ⟨_, h⟩ := h
  have R := VG.Proof.Rsa.X86.InvBatchRt.Time.leaf (B := g.B) (Z := g.Z) (P := Both (P g)) (τE ds)
    (fun s t ⟨ps, pt⟩ => agreeE hds (hpre s ps) (hpre t pt)
      (fun d hd => (hval s ps d hd).trans (hval t pt d hd).symm))
    (fun s t ⟨ps, pt⟩ => by
      obtain ⟨_, _, ⟨a, _⟩, K, _⟩ := hpre s ps
      obtain ⟨_, _, ⟨b, _⟩, L, _⟩ := hpre t pt
      exact ⟨K.2.2 ▸ a.ws.workspace.wr, L.2.2 ▸ b.ws.workspace.wr⟩)
    (fun s t ⟨ps, pt⟩ => ⟨run_of (hf g.vw _ (hv s ps)), run_of (hf g.vw _ (hv t pt))⟩) h
  exact (RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf g s ps, hf g t pt⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

/-! ## A digit step -/

/-- The square root's public facts: `n`'s length `a` in argument `nl`, `1 ≤ a ≤ 1024`, `W' ≤ w`. -/
def SqG (g : Geo) (a : Nat) : Prop := g.args nl = BitVec.ofNat 32 a ∧ wq a ≤ g.w ∧ a ≤ 1024 ∧ 1 ≤ a

/-- A digit step's start, `j` digits left. -/
def SQ (g : Geo) (a j : Nat) (u : State) : Prop :=
  SqG g a ∧ 1 ≤ j ∧ j < wq a ∧ P0 g u ∧ ∃ s0 A V0 X, SqI g s0 A V0 a X j u

/-- Between a digit step's leaves: a leaf's start, `j` in `sCt`. -/
def SW (g : Geo) (a j : Nat) (u : State) : Prop :=
  SqG g a ∧ 1 ≤ j ∧ j < wq a ∧ P0 g u ∧ slot u.mem g.B sCt = j

/-- Inside `fixX`, after its add loop: `edi` its count, the mask in `hCnt`. -/
def SF (g : Geo) (a j : Nat) (v : State) : Prop :=
  SqG g a ∧ 1 ≤ j ∧ j < wq a ∧ ∃ s, P0 g s ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v ∧
    Outside g.B 0 g.Z s.mem v.mem ∧ slot v.mem g.B sCt = j ∧
    ∃ cb, BitVec.ofNat 32 (slot v.mem g.B hCnt) = VG.Proof.Bignum.X86.R2Words.bmask cb

section
variable {g : Geo} {a j : Nat} {u : State}

theorem SQ.onView (h : SQ g a j u) : SQ g.vw a j (view u g.B g.Z) :=
  let ⟨ga, j1, j2, p, _, A, V0, X, AW, V, s, r, k, r1, r2, r3⟩ := h
  ⟨ga, j1, j2, p.view, _, A, V0, X, AW, V, s, r, k.onView, r1, r2, r3⟩

theorem SQ.sct (h : SQ g a j u) : slot u.mem g.B sCt = j :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, k, _, hC, _⟩ := h
  (k.sl sCt (by simp)).trans hC

theorem SW.onView (h : SW g a j u) : SW g.vw a j (view u g.B g.Z) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.view, h.2.2.2.2⟩

theorem SF.onView (h : SF g a j u) : SF g.vw a j (view u g.B g.Z) := by
  obtain ⟨ga, j1, j2, s, p, K, O, hC, hd⟩ := h
  exact ⟨ga, j1, j2, view s g.B g.Z, p.view, ⟨K.1, by simp only [view, State.withRegions_rd, K.2.1, K.2.2],
    rfl⟩, O, hC, hd⟩

theorem SF.ediFree (h : SF g a j u) : EdiFree g u :=
  let ⟨_, _, _, s, p, K, O, _⟩ := h
  ⟨s, _, p, K, by decide, O⟩

theorem SqG.mlen (ga : SqG g a) (h : P0 g u) : MLen u g.B g.Z nl a := by
  have := h.2.2.arguments nl (by decide)
  rw [ga.1] at this
  exact ⟨this, ga.2.2.1⟩

/-- `W' + 3` words fit in a wide array. -/
theorem SqG.kw (ga : SqG g a) : 2 * wq a + 2 ≤ kw (16 * g.n + 24) := by
  rw [kw_wid]; have := ga.2.1; change 2 * wq a + 2 ≤ 2 * (2 * g.n + 2) + 2; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width] at this; omega

/-- A step to a state that keeps the frame, `sCt` outside what it writes. -/
theorem P0.next {s t : State} {rs : List Reg} (h : P0 g s) (ht : RtWs wid t g.B g.Z (16 * g.n + 24) 22)
    (K : Keeps rs s t) (sp : .esp ∉ rs) (O : Outside g.B 0 g.Z s.mem t.mem) : P0 g t :=
  ⟨ht, h.2.1, h.2.2.keep K sp O⟩

end

/-- `fixX`'s head, add loop and tail. -/
abbrev fixHd : Prog isa := .block (winPtrs ++ VG.Impl.Rsa.X86.KeyRt.arrPtr wid .ebp sqT .eax ++
  ([.mov .eax (.reg .ebp), .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)),
    .alu .add .eax (.reg .eax), .alu .sbb .ecx (.reg .ecx), .store (sc hCnt) .ecx,
    .mov .esi (.imm 0), .mov .edi (.reg .edx), .alu .add .edi (.imm 4)] : List Instr))
abbrev fixLp : Prog isa := .loop (.block VG.Impl.Bignum.X86.R2Words.addBody) .ne
abbrev fixTl : Prog isa := .block (VG.Impl.Rsa.X86.KeyRt.restoreEdi wid ++ winPtrs ++
  ([.mov .ecx (.mem (sc hCnt)), .alu .and .ecx (.imm 2), .mov .eax (.mem (at_ .ebx 0)),
    .mov .edx (.mem (at_ .ebx 4)), .alu .sub .eax (.reg .ecx), .alu .sbb .edx (.imm 0),
    .store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx] : List Instr))

theorem fixX_eq : fixX = .seq fixHd (.seq fixLp fixTl) := rfl

/-- `stepX`'s last block: `sCt` down by one. -/
abbrev decCt : List Instr := [.mov .eax (.mem (sc sCt)), .alu .sub .eax (.imm 1), .store (sc sCt) .eax]

/-! ### The leaves' runs -/

section
variable {g : Geo} {a j : Nat} {u : State}

theorem est_w (h : SQ g a j u) : WP isa (.block estX) u (SW g a j) := by
  have hC := h.sct
  obtain ⟨ga, j1, j2, p, _, _, _, _, hI⟩ := h
  refine WP.mono (estX_sq hI ga.1 ga.2.2.1 ga.2.1 j1 j2) fun v ⟨hv, k, K⟩ => ⟨ga, j1, j2,
    p.next hv K (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside p.1.ws k (by simp) (by decide)), ?_⟩
  rw [k.slot (by decide) (by decide)]; exact hC

theorem ms_w (h : SW g a j u) : WP isa mulSubX u (SW g a j) := by
  obtain ⟨ga, j1, j2, p, hC⟩ := h
  have hW := ga.kw
  refine WP.mono (mulSubX_ok p.1 (ga.mlen p) hC j1 j2 (by omega) rfl) fun v ⟨hv, k, _, _, _, K⟩ => ⟨ga, j1, j2,
    p.next hv K (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside p.1.ws k (by decide) (by simp)), ?_⟩
  rw [k.slot (by decide) (by simp)]; exact hC

/-- `D`'s window, `T` and `Z` inside the working space. -/
theorem P0.fits (h : P0 g u) :
    arr (kw (16 * g.n + 24)) sqD + 4 * (kw (16 * g.n + 24) + 2) ≤ g.Z ∧
      arr (kw (16 * g.n + 24)) sqZ + 4 * (kw (16 * g.n + 24) + 2) ≤ g.Z ∧
      160 ≤ arr (kw (16 * g.n + 24)) sqD ∧ 160 ≤ arr (kw (16 * g.n + 24)) sqZ := by
  have fd := h.1.ws.arr_fit (j := sqD) (by decide)
  have fz := h.1.ws.arr_fit (j := sqZ) (by decide)
  simp only [S] at fd fz
  refine ⟨fd, fz, ?_, ?_⟩ <;> simp only [arr, VG.Impl.Rsa.X86.Keys.hdr] <;> omega

theorem toE_w (h : SW g a j u) : WP isa (.block toE) u (SW g a j) := by
  have F := h.2.2.2.1.fits
  obtain ⟨ga, j1, j2, p, hC⟩ := h
  have hW := ga.kw
  refine WP.mono (toE_ok p.1 (ga.mlen p) hC j1 j2 (by omega)) fun v ⟨hv, O, _, K⟩ => ⟨ga, j1, j2,
    p.next hv K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_⟩
  rw [slot, O.w32 (.inl (by simp only [sCt]; omega)) (by simp only [sCt]; omega)]; exact hC

theorem upd_w (h : SW g a j u) : WP isa (.block updX) u (SW g a j) := by
  have F := h.2.2.2.1.fits
  obtain ⟨ga, j1, j2, p, hC⟩ := h
  have hW := ga.kw
  refine WP.mono (updX_ok p.1 (ga.mlen p) hC j1 j2 (by omega)) fun v ⟨hv, O, _, K⟩ => ⟨ga, j1, j2,
    p.next hv K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_⟩
  rw [slot, O.w32 (.inl (by simp only [sCt]; omega)) (by simp only [sCt]; omega)]; exact hC

theorem cb_w (h : SW g a j u) : WP isa copyBackX u (SW g a j) := by
  have F := h.2.2.2.1.fits
  obtain ⟨ga, j1, j2, p, hC⟩ := h
  have hW := ga.kw
  refine WP.mono (copyBackX_ok p.1 (ga.mlen p) hC j1 j2 (by omega)) fun v ⟨hv, O, _, K⟩ => ⟨ga, j1, j2,
    p.next hv K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_⟩
  rw [slot, O.w32 (.inl (by simp only [sCt]; omega)) (by simp only [sCt]; omega)]; exact hC

theorem fixHL_w (h : SW g a j u) : WP isa (.seq fixHd fixLp) u (SF g a j) := by
  obtain ⟨ga, j1, j2, p, hC⟩ := h
  have hW := ga.kw
  exact WP.mono (fixHL_ok p.1 (ga.mlen p) hC j1 j2 (by omega)) fun v ⟨K, O, hC', d⟩ =>
    ⟨ga, j1, j2, u, p, K, O, hC', d⟩

theorem fixTl_w (h : SF g a j u) : WP isa fixTl u (SW g a j) := by
  obtain ⟨ga, j1, j2, s, p, K, O, hC, cb, hd⟩ := h
  have F := p.fits
  have hW := ga.kw
  refine fixTail_ok p.1 (ga.mlen p) j1 j2 (by omega) K O hC hd fun t Kt Ot _ => ?_
  have Ot' : Outside g.B 0 g.Z s.mem t.mem := O.trans (Ot.mono (Nat.zero_le _) (by omega))
  refine ⟨ga, j1, j2, p.next (p.1.keep Kt (by decide) (by decide) Ot') Kt (by decide) Ot', ?_⟩
  rw [slot, Ot.w32 (.inl (by simp only [sCt]; omega)) (by simp only [sCt]; omega)]; exact hC

theorem dec_w (h : SW g a j u) : WP isa (.block decCt) u fun _ => True := by
  have ws := h.2.2.2.1.1.ws
  refine wp_movS (readHdr ws (by decide)) fun s₁ U₁ _ => ?_
  refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun s₂ U₂ _ => ?_
  exact storeHdr (ws.rest (U₁.keeps.trans U₂.keeps)) (by decide) .eax fun _ _ _ _ _ _ => WP.block_nil trivial

end

/-! ### The step, related -/

theorem c_est : OkK [sCt] (.block estX) := ⟨_, by taint_decide⟩
theorem c_ms : OkK [sCt] mulSubX := ⟨_, by taint_decide⟩
theorem c_toE : OkK [sCt] (.block toE) := ⟨_, by taint_decide⟩
theorem c_fhl : OkK [sCt] (.seq fixHd fixLp) := ⟨_, by taint_decide⟩
theorem c_ftl : OkE [sCt] fixTl := ⟨_, by taint_decide⟩
theorem c_upd : OkK [sCt] (.block updX) := ⟨_, by taint_decide⟩
theorem c_cb : OkK [sCt] copyBackX := ⟨_, by taint_decide⟩
theorem c_dec : OkK [sCt] (.block decCt) := ⟨_, by taint_decide⟩

section
variable {g : Geo} {a j : Nat}

/-- A leaf between a digit step's leaves. -/
theorem leafSW {Q : Geo → State → Prop} {c : Prog isa} (hf : ∀ g' u, SW g' a j u → WP isa c u (Q g'))
    (h : OkK [sCt] c) : RelCT isa (Both (SW g a j)) c (Both (Q g)) :=
  leafP (fun _ => j) (by decide) (fun _ h => h.2.2.2.1) (fun _ h => h.onView)
    (fun _ h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact h.2.2.2.2) hf h

theorem fixX_rel : RelCT isa (Both (SW g a j)) fixX (Both (SW g a j)) := by
  rw [fixX_eq]
  exact relSeqs (x := fixHd) (xs := [fixLp]) (y := fixTl) (ys := [])
    (leafSW (fun _ _ h => fixHL_w h) c_fhl)
    (leafE (fun _ => j) (by decide) (fun _ h => h.ediFree) (fun _ h => h.onView)
      (fun _ h d hd => by
        obtain ⟨_, _, _, _, _, _, _, hC, _⟩ := h
        simp only [List.mem_singleton] at hd; subst hd; exact hC)
      (fun _ _ h => fixTl_w h) c_ftl)

/-- A digit step, related. -/
theorem stepX_rel : RelCT isa (Both (SQ g a j)) stepX (fun _ _ => True) := by
  have e : stepX = .seq (.block estX) (.seq mulSubX (.seq (.block toE) (.seq fixX (.seq fixX (.seq fixX
      (.seq (.block updX) (.seq copyBackX (.block decCt)))))))) := rfl
  rw [e]
  refine VG.RelCT.seq (leafP (P := fun g' => SQ g' a j) (Q := fun g' => SW g' a j) (fun _ => j) (by decide)
    (fun _ h => h.2.2.2.1) (fun _ h => h.onView)
    (fun _ h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact h.sct)
    (fun _ _ h => est_w h) c_est) ?_
  refine VG.RelCT.seq (leafSW (fun _ _ h => ms_w h) c_ms) (VG.RelCT.seq (leafSW (fun _ _ h => toE_w h) c_toE)
    (VG.RelCT.seq fixX_rel (VG.RelCT.seq fixX_rel (VG.RelCT.seq fixX_rel
    (VG.RelCT.seq (leafSW (fun _ _ h => upd_w h) c_upd) (VG.RelCT.seq (leafSW (fun _ _ h => cb_w h) c_cb)
    ((leafSW (Q := fun _ _ => True) (fun _ _ h => dec_w h) c_dec).mono (fun _ _ h => h) fun _ _ _ => trivial)))))))

end

/-! ## Frames between the leaves -/

/-- Two postconditions of one run. -/
theorem wp_both {c : Prog isa} {s : State} {P Q : State → Prop} (hp : WP isa c s P) (hq : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨tr, t, e, p⟩ := hp
  obtain ⟨_, _, e', q⟩ := hq
  obtain ⟨_, rfl⟩ := Exec.det e e'
  exact ⟨tr, t, e, p, q⟩

/-- A frame of the square root: the arrays `live`, `liveW`, the header words `ls`, their values `F`. -/
def QW (a : Nat) (live liveW ls : List Nat) (F : (Nat → Nat) → (Nat → Nat) → Prop) (g : Geo) (s : State) :
    Prop :=
  SqG g a ∧ ∃ s0 A AW V, KS g s0 A live AW liveW V ls s ∧ F AW V

section
variable {a : Nat} {live liveW ls : List Nat} {F : (Nat → Nat) → (Nat → Nat) → Prop} {g : Geo} {s : State}

theorem QW.onView (h : QW a live liveW ls F g s) : QW a live liveW ls F g.vw (view s g.B g.Z) :=
  let ⟨ga, _, A, AW, V, k, f⟩ := h
  ⟨ga, _, A, AW, V, k.onView, f⟩

theorem QW.p0 (pg : PubG g) (h : QW a live liveW ls F g s) : P0 g s :=
  let ⟨_, _, _, _, _, k, _⟩ := h
  k.pre0 pg

end

/-- A leaf from a frame of the square root. -/
theorem leafQ {a : Nat} {g : Geo} (pg : PubG g) {live liveW ls : List Nat}
    {F : (Nat → Nat) → (Nat → Nat) → Prop} {Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat}
    (vals : Nat → Nat) (hds : ∀ d ∈ ds, d ∈ ls ∧ d + 4 ≤ 160) (hv : ∀ AW V, F AW V → ∀ d ∈ ds, V d = vals d)
    (hf : ∀ g' s, QW a live liveW ls F g' s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (QW a live liveW ls F g)) c (Both (Q g)) :=
  leafP vals (fun d hd => (hds d hd).2) (fun _ h => h.p0 pg) (fun _ h => h.onView)
    (fun _ h d hd => by
      obtain ⟨_, _, _, AW, V, k, f⟩ := h
      exact (k.sl d (hds d hd).1).trans (hv AW V f d hd)) hf h

/-- A bit stage of `b` bits, its flag set. -/
abbrev QB (a b : Nat) (live liveW ls : List Nat) : Geo → State → Prop :=
  QW a live liveW ls fun _ V => V sStg ≤ 1 ∧ V sB = b

/-- Inside a bit stage's `timesH`, before run `i` (or, `Post`, before its count down). -/
abbrev QT (a b : Nat) (live liveW ls : List Nat) (i : Nat) : Geo → State → Prop :=
  QW a live liveW (sBc :: ls) fun _ V => V sBc = b - i ∧ V sStg ≤ 1 ∧ V sB = b

theorem c_bc0 : OkK [sB] (.block [.mov .eax (.mem (sc sB)), .store (sc sBc) .eax]) := ⟨_, by taint_decide⟩
theorem c_bcd : OkK [sBc] (.block downBc) := ⟨_, by taint_decide⟩

/-- `timesH body` on a bit stage's frame, `body` keeping it. -/
theorem sqTimes {a b : Nat} {g : Geo} (pg : PubG g) {live liveW ls : List Nat} {body : Prog isa}
    (hb : 0 < b) (hb32 : b < 2 ^ 32) (hB : sB ∈ ls) (cb : OkK [] body)
    (hstep : ∀ g' s0 A AW V s, KS g' s0 A live AW liveW V (sBc :: ls) s →
      WP isa body s fun t => ∃ A' AW', KS g' s0 A' live AW' liveW V (sBc :: ls) t) :
    RelCT isa (Both (QB a b live liveW ls g)) (timesH body) (Both (QB a b live liveW ls g)) := by
  have nS : sStg ≠ sBc := by decide
  have nB : sB ≠ sBc := by decide
  refine relTimesH (fun g' i => QT a b live liveW ls i g') (fun g' i => QT a b live liveW ls i g') hb hb32
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨_, _, _, _, _, h, f⟩ => ⟨h.ws, by rw [h.sl sB hB, f.2]⟩)
    (fun _ _ _ ⟨ga, s0, A, AW, _, h, f⟩ k e r =>
      ⟨ga, s0, A, AW, _, h.slot1 k (by decide) (r.mono (by decide)) e, by rw [upd_self, Nat.sub_zero],
        by rw [upd_ne _ _ nS]; exact f.1, by rw [upd_ne _ _ nB]; exact f.2⟩)
    (fun _ _ _ _ ⟨_, _, _, _, _, h, f⟩ => ⟨h.ws, by rw [h.sl sBc (by simp), f.1]⟩)
    (fun _ _ _ _ _ ⟨ga, s0, A, AW, _, h, f⟩ k e r => by
      have h' := (h.slot1 k (by decide) r e).mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
        (fun _ he => ⟨List.mem_cons_of_mem _ he, rfl⟩)
      refine ⟨fun _ => ⟨ga, s0, A, AW, _, h', by rw [upd_self], by rw [upd_ne _ _ nS]; exact f.2.1,
          by rw [upd_ne _ _ nB]; exact f.2.2⟩, fun _ => ⟨ga, s0, A, AW, _, h'.mono (fun _ hj => ⟨hj, rfl⟩)
          (fun _ hj => ⟨hj, rfl⟩) (fun _ hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩),
          by rw [upd_ne _ _ nS]; exact f.2.1, by rw [upd_ne _ _ nB]; exact f.2.2⟩⟩)
    (fun _ _ => leafQ pg (fun _ => 0) (ds := []) (by simp) (by simp)
      (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ =>
        WP.mono (hstep g' s0 A AW V s h) fun _ ⟨A', AW', h'⟩ => ⟨ga, s0, A', AW', V, h', f⟩) cb)
    c_bc0 c_bcd

/-! ## `normX` -/

/-- A bit stage's test of `normX`. -/
abbrev nbH1 : Prog isa := .block (topH .esi sqZ 1 .edx ++ ([.mov .eax (.mem (at_ .esi 0))] : List Instr))
abbrev nbH3 : Prog isa := .block (flagZero ++ ([.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)),
  .alu .and .edx (.mem (sc sB)), .alu .add .edx (.mem (sc sZb)), .store (sc sZb) .edx] : List Instr))
abbrev nbHead : List (Prog isa) := [nbH1, topTest, nbH3]

/-- `normX`'s bit stage. -/
abbrev nbBody : Prog isa := seqs (nbHead ++ [upBitsSelH sqZ])

/-- `stageXB_head` without the values: the flag set and `sZb` written. -/
theorem nbHead_w {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {a b : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] V (sB :: lsN) s) (hm : MLen s g.B g.Z nl a) (ha0 : 1 ≤ a)
    (haw : wq a ≤ g.w) (hV : V sB = b) (hb0 : 0 < b) (hb : b < 32) :
    WP isa (seqs nbHead) s fun t => ∃ V', KS g s0 A [aD, aZero] AW [wR] V' (sZb :: sStg :: sB :: lsN) t ∧
      V' sStg ≤ 1 ∧ V' sB = b := by
  simp only [seqs]
  refine WP.seq (WP.mono (h.readTop hm ha0 haw) fun t₁ ⟨h₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (topTest_ok h₁.ws (b := b) (by rw [h₁.sl _ (by simp), hV]) hb0 hb)
    fun t₂ ⟨K₂, m₂, _⟩ => ?_)
  have h₂ := h₁.of_rest K₂ (by decide) m₂
  refine WP.block_append (WP.mono h₂.flagZero fun t₃ ⟨h₃, _⟩ => ?_)
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have h₃₁ := h₃.of_rest U₁.keeps (by decide) U₁.mem
  refine wp_subS (h₃₁.readSlot (d := sStg) (by simp)) fun u₂ U₂ _ => ?_
  have h₃₂ := h₃₁.of_rest U₂.keeps (by decide) U₂.mem
  refine wp_logicS (.inl rfl) (h₃₂.readSlot (d := sB) (by simp)) fun u₃ U₃ => ?_
  have h₃₃ := h₃₂.of_rest U₃.keeps (by decide) U₃.mem
  refine wp_addS (h₃₃.readSlot (d := sZb) (by simp)) fun u₄ U₄ _ => ?_
  have h₃₄ := h₃₃.of_rest U₄.keeps (by decide) U₄.mem
  refine WP.mono (h₃₄.storeSlot (d := sZb) (by decide) .edx) fun t₄ ⟨h₄, _, _⟩ => ⟨_, h₄, ?_, ?_⟩
  · rw [upd_ne _ _ (by decide), upd_self]; split <;> decide
  · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hV]

theorem c_nbHead : OkK [sB] (seqs nbHead) := ⟨_, by taint_decide⟩
theorem c_cpZ : OkK [] (copy wid wT sqZ) := ⟨_, by taint_decide⟩
theorem c_dblTX : OkK [] (chain wid .adc wT wT wT false) := ⟨_, by taint_decide⟩
theorem c_selZ : OkK [] (sel wid sqZ sqZ wT sStg) := ⟨_, by taint_decide⟩

/-- The header words inside `normX`'s bit stage. -/
abbrev nbL : List Nat := sZb :: sStg :: sB :: lsN

/-- A bit stage of `normX`, related: its run's values aside. -/
theorem nbBody_rel {g : Geo} (pg : PubG g) {a j : Nat} (hj : 2 ^ j < 32) :
    RelCT isa (Both (QW a [aD, aZero] [wR] (sB :: lsN) (fun _ V => V sB = 2 ^ j) g)) nbBody (fun _ _ => True) := by
  have hb : 0 < 2 ^ j := Nat.two_pow_pos j
  refine relSeqs (x := nbH1) (xs := [topTest, nbH3]) (y := upBitsSelH sqZ) (ys := [])
    (R := Both (QB a (2 ^ j) [aD, aZero] [wR] nbL g))
    (leafQ pg (fun _ => 2 ^ j) (by decide) (fun _ V f d hd => by simp only [List.mem_singleton] at hd; subst hd; exact f)
      (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ => WP.mono (nbHead_w h (h.mlen ga.1 ga.2.2.1) ga.2.2.2 ga.2.1 f hb hj)
        fun _ ⟨V', h', f'⟩ => ⟨ga, s0, A, AW, V', h', f'⟩) c_nbHead) ?_
  show RelCT isa _ (.seq (copy wid wT sqZ) (.seq (timesH (chain wid .adc wT wT wT false))
    (sel wid sqZ sqZ wT sStg))) _
  refine VG.RelCT.seq (leafQ (Q := QB a (2 ^ j) [aD, aZero] [wT, wR] nbL) pg (fun _ => 0) (ds := []) (by simp)
    (by simp) (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ => WP.mono (h.copy_W (o := wT) (a := wR) (by decide) (by simp)
      (by decide) (by decide)) fun _ ⟨h', _⟩ => ⟨ga, s0, A, _, V, h', f⟩) c_cpZ) ?_
  refine VG.RelCT.seq (sqTimes pg hb (by omega) (by simp) c_dblTX fun g' s0 A AW V s h =>
    WP.mono (h.add_W (o := wT) (a := wT) (b := wT) (by decide) (by simp) (by simp) (by decide))
      fun _ ⟨hv, _⟩ => ⟨A, _, hv.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
        (fun _ hd => ⟨hd, rfl⟩)⟩) ?_
  exact (leafQ (Q := fun _ _ => True) pg (fun _ => 0) (ds := []) (by simp) (by simp)
    (fun g' s ⟨_, _, _, _, _, h, f⟩ => WP.mono (h.sel_W (o := sqZ) (a := sqZ) (b := wT) (sl := sStg) (by decide)
      (by decide) (by decide) (by simp) f.1 (.inr (by decide)) (by decide)) fun _ _ => trivial) c_selZ).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-- A relation whose post each run meets by its own correctness lemma. -/
theorem relAug {P S : State → Prop} {Q : State → State → Prop} {c : Prog isa} (R : RelCT isa (Both P) c Q)
    (hf : ∀ s, P s → WP isa c s S) : RelCT isa (Both P) c (Both S) :=
  (VG.RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf s ps, hf t pt⟩)).mono (fun _ _ h => h) (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

/-- Before or after a word stage of `normX` (`WSt`), its values hidden. -/
def NW (a e c4 : Nat) (g : Geo) (t : State) : Prop :=
  SqG g a ∧ ∃ s0 A V X zf, 1 ≤ X + zf ∧ WSt g s0 A V X a zf e c4 t

/-- Before or after a bit stage of `normX` (`BSt`), its values hidden. -/
def NB (a e bv : Nat) (g : Geo) (t : State) : Prop :=
  SqG g a ∧ ∃ s0 A V X zf, BSt g s0 A V X a zf e bv t

/-- After `zeroX`: the word stages' start. -/
def NZ (a : Nat) (g : Geo) (t : State) : Prop :=
  SqG g a ∧ ∃ s0 A AW V X zf, KS g s0 A [aD, aZero] AW [wR] V lsN t ∧ V sZf = zf ∧ V sKw = 0 ∧
    V sZb = 0 ∧ AW wR = X + zf ∧ X + zf < 2 ^ (64 * wq a) ∧ 1 ≤ X + zf

section
variable {a e c4 bv : Nat} {g : Geo} {t : State}

theorem NW.onView (h : NW a e c4 g t) : NW a e c4 g.vw (view t g.B g.Z) :=
  let ⟨ga, _, A, V, X, zf, h1, AW, V', k, r⟩ := h
  ⟨ga, _, A, V, X, zf, h1, AW, V', k.onView, r⟩

theorem NW.p0 (pg : PubG g) (h : NW a e c4 g t) : P0 g t :=
  let ⟨_, _, _, _, _, _, _, _, _, k, _⟩ := h
  k.pre0 pg

theorem NB.onView (h : NB a e bv g t) : NB a e bv g.vw (view t g.B g.Z) :=
  let ⟨ga, _, A, V, X, zf, AW, V', k, r⟩ := h
  ⟨ga, _, A, V, X, zf, AW, V', k.onView, r⟩

theorem NB.p0 (pg : PubG g) (h : NB a e bv g t) : P0 g t :=
  let ⟨_, _, _, _, _, _, _, _, k, _⟩ := h
  k.pre0 pg

theorem NZ.onView (h : NZ a g t) : NZ a g.vw (view t g.B g.Z) :=
  let ⟨ga, _, A, AW, V, X, zf, k, r⟩ := h
  ⟨ga, _, A, AW, V, X, zf, k.onView, r⟩

theorem NZ.p0 (pg : PubG g) (h : NZ a g t) : P0 g t :=
  let ⟨_, _, _, _, _, _, _, k, _⟩ := h
  k.pre0 pg

end

theorem c_xsInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * 2 ^ 8))), .store (sc sC4) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_xsLim : OkK [sC4] (.block ((VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
    ([.alu .add .eax (.reg .eax)] : List Instr)) ++
    ([.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)] : List Instr))) :=
  ⟨_, by taint_decide⟩
theorem c_xsHalf : OkK [sC4] (.block halfC4) := ⟨_, by taint_decide⟩
theorem c_stageXWH : OkK [sC4] stageXWH := ⟨_, by taint_decide⟩
theorem c_xbInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (2 ^ 4))), .store (sc sB) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_xbHalf : OkK [sB] (.block (halfB 1)) := ⟨_, by taint_decide⟩

/-- `normX`'s word stages, related. -/
theorem nwStages_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (NZ a g)) (wordStagesL 256 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
      ([.alu .add .eax (.reg .eax)] : List Instr)) stageXWH) (Both (NW a 1 2 g)) := by
  have e : wordStagesL 256 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++ ([.alu .add .eax (.reg .eax)] : List Instr))
      stageXWH = wordStagesL (2 ^ 8) (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
        ([.alu .add .eax (.reg .eax)] : List Instr)) stageXWH := rfl
  rw [e]
  refine relWordStagesL (lim := 8 * wq a) (S := NZ a) (Fin := NW a 1 2)
    (fun g' j => NW a (2 ^ (j + 1)) (4 * 2 ^ j) g') (fun g' j => NW a (2 ^ j) (4 * 2 ^ j) g') (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ _ h => h.p0 pg)
    (fun _ h => h.onView) (fun _ _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨_, _, _, _, _, _, _, k, _⟩ => k.ws) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ c_xsInit c_xsLim c_xsHalf
  · rintro g' s u ⟨ga, s0, A, AW, V, X, zf, h, hz, hK, hZ, hv, hlt, h1⟩ k hs K
    have hwq : wq a ≤ 256 := by simp only [wq]; have := ga.2.2.1; omega
    refine ⟨ga, s0, A, V, X, zf, h1, wst_init h (fun _ _ => rfl) hz hK hZ hv hlt ?_ k hs (K.mono (by decide))⟩
    rw [show 2 * wq a - 2 ^ (8 + 1) = 0 by omega, Nat.mul_zero, Nat.pow_zero]; exact h1
  · rintro g' j u - ⟨_, _, _, _, _, _, _, AW', V', hu, -, -, -, hC, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hC]⟩
  · rintro g' j u - ⟨ga, _, _, _, _, _, _, AW', V', hu, -⟩ is Q k
    have hwq : wq a ≤ 256 := by simp only [wq]; have := ga.2.2.1; omega
    rw [List.append_assoc]
    refine VG.Proof.Rsa.X86.WordRt.width4_ok (hu.mlen ga.1 ga.2.2.1) fun v U m e => wp_addS rfl fun w W _ => ?_
    refine k w ((U.mono (by decide)).trans (W.keeps.mono (by decide))) (by rw [W.mem, m]) ?_
    rw [W.gpr, e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rintro g' j u v - ⟨ga, s0, A, V, X, zf, h1, AW', V', hu, r⟩ K m
    exact ⟨ga, s0, A, V, X, zf, h1, AW', V', hu.of_rest K (fun x hx => hx) m, r⟩
  · rintro g' j u - ⟨ga, s0, A, V, X, zf, h1, AW', V', hu, hsq', hz', hzb', hC, hv', hlt', -⟩ hj
    refine ⟨ga, s0, A, V, X, zf, h1, AW', V', hu, hsq', hz', hzb', hC, hv', hlt', ?_⟩
    rw [show 2 * wq a - 2 ^ j = 0 by omega, Nat.mul_zero, Nat.pow_zero]
    rw [hv']; exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  · rintro g' j u - ⟨_, _, _, _, _, _, _, AW', V', hu, -, -, -, hC, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hC]⟩
  · rintro g' j u v _ ⟨ga, s0, A, V, X, zf, h1, P⟩ k hs K
    refine ⟨fun hj => ⟨ga, s0, A, V, X, zf, h1, ?_⟩, fun hj => ⟨ga, s0, A, V, X, zf, h1, ?_⟩⟩
    · have P' := P.reslot k hs K
      have e : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      rw [show j - 1 + 1 = j by omega, show 4 * 2 ^ (j - 1) = 2 * 2 ^ j by omega]
      exact P'
    · subst hj
      exact P.reslot k hs K
  · intro j _ hl
    refine leafP (P := fun g' => NW a (2 ^ (j + 1)) (4 * 2 ^ j) g') (Q := fun g' => NW a (2 ^ j) (4 * 2 ^ j) g')
      (fun _ => 4 * 2 ^ j) (by decide) (fun _ h => h.p0 pg) (fun _ h => h.onView) ?_ ?_ c_stageXWH
    · rintro _ ⟨_, _, _, _, _, _, _, AW', V', hu, -, -, -, hC, -⟩ d hd
      simp only [List.mem_singleton] at hd; subst hd
      exact (hu.sl _ (by simp)).trans hC
    · rintro g' u ⟨ga, s0, A, V, X, zf, h1, P⟩
      exact WP.mono (wordStage_ok ga.1 ga.2.2.1 ga.2.1 h1 (by omega) P) fun _ P' => ⟨ga, s0, A, V, X, zf, h1, P'⟩

/-- `normX`'s bit stages, related. -/
theorem nbStages_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (NW a 1 2 g)) (bitStagesL 16 2 nbBody) (Both (NB a 2 1 g)) := by
  have e : bitStagesL 16 2 nbBody = bitStagesL (2 ^ 4) (2 ^ 1) nbBody := rfl
  rw [e]
  refine relBitStagesL (S := NW a 1 2) (Fin := NB a 2 1)
    (fun g' j => NB a (2 ^ (j + 1)) (2 ^ j) g') (fun g' j => NB a (2 ^ j) (2 ^ j) g') (by decide) (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨_, _, _, _, _, _, _, _, _, k, _⟩ => k.ws) ?_ ?_ ?_ ?_ c_xbInit c_xbHalf
  · rintro g' s u ⟨ga, s0, A, V, X, zf, _, P⟩ k e K
    have hwq : 1 ≤ wq a := by simp only [wq]; have := ga.2.2.2; omega
    exact ⟨ga, s0, A, V, X, zf, bst_init hwq P k e (K.mono (by decide))⟩
  · rintro g' j u - - ⟨_, _, _, _, _, _, AW', V', hu, -, -, hB, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hB]⟩
  · rintro g' j u v _ _ ⟨ga, s0, A, V, X, zf, Q⟩ k e K
    refine ⟨fun hj => ⟨ga, s0, A, V, X, zf, ?_⟩, fun hj => ⟨ga, s0, A, V, X, zf, ?_⟩⟩
    · have Q' := Q.reslot k e K
      have e2 : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      rw [show j - 1 + 1 = j by omega, show 2 ^ (j - 1) = 2 ^ j / 2 by omega]
      exact Q'
    · subst hj
      exact Q.reslot k e K
  · intro j hm hj
    have b32 : 2 ^ j < 32 := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hj; simp at this; omega
    refine relAug ((nbBody_rel (a := a) pg b32).mono (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩) (fun _ _ h => h)) ?_
    · obtain ⟨ga, s0, A, _, _, _, AW', V', hu, -, -, hB, -⟩ := hs
      exact ⟨ga, s0, A, AW', V', hu, hB⟩
    · obtain ⟨ga, s0, A, _, _, _, AW', V', hu, -, -, hB, -⟩ := ht
      exact ⟨ga, s0, A, AW', V', hu, hB⟩
    · rintro u ⟨ga, s0, A, V, X, zf, P⟩
      exact WP.mono (bitStage_ok ga.1 ga.2.2.1 ga.2.2.2 ga.2.1 hm hj P) fun _ P' => ⟨ga, s0, A, V, X, zf, P'⟩

/-- Before `normX`. -/
abbrev N0 (a : Nat) : Geo → State → Prop := QW a [aD, aZero] [wR] sqSlotsW fun _ _ => True

/-- After `clearAboveH`. -/
abbrev N1 (a : Nat) : Geo → State → Prop := QW a [aD, aZero] [wR] sqSlotsW fun AW _ => AW wR < 2 ^ (64 * wq a)

theorem c_clr : OkK [] clearAboveH := ⟨_, by taint_decide⟩
theorem c_zx : OkK [] zeroX := ⟨_, by taint_decide⟩

/-- `normX`, related: its run's values aside. -/
theorem normX_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (N0 a g)) normX (fun _ _ => True) := by
  have e : normX = .seq clearAboveH (.seq zeroX (.seq (wordStagesL 256
      (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++ ([.alu .add .eax (.reg .eax)] : List Instr)) stageXWH)
      (bitStagesL 16 2 nbBody))) := rfl
  rw [e]
  refine VG.RelCT.seq (leafQ (Q := N1 a) pg (fun _ => 0) (ds := []) (by simp) (by simp)
    (fun g' s ⟨ga, s0, A, AW, V, h, _⟩ => WP.mono (h.clearAbove_ok (by simp) (h.mlen ga.1 ga.2.2.1) ga.2.1
      (by decide)) fun _ h' => ⟨ga, s0, A, _, V, h', show upd AW wR _ wR < _ by
      rw [upd_self]; exact Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
    c_clr) ?_
  refine VG.RelCT.seq (leafQ (Q := NZ a) pg (fun _ => 0) (ds := []) (by simp) (by simp)
    (fun g' s ⟨ga, s0, A, AW, V, h, hlt⟩ => WP.mono (zeroX_ok h rfl)
      fun _ ⟨AW₂, V₂, h₂, _, hz₂, hK₂, hZ₂, hv₂⟩ => by
        have hlt' : AW wR < 2 ^ (64 * wq a) := hlt
        have hw : 1 ≤ 64 * wq a := by simp only [wq]; have := ga.2.2.2; omega
        refine ⟨ga, s0, A, AW₂, V₂, AW wR, V₂ sZf, h₂, rfl, hK₂, hZ₂, hv₂, ?_, ?_⟩ <;> rw [hz₂] <;> split
        · rename_i e; rw [e]; exact Nat.one_lt_two_pow (by omega)
        all_goals omega) c_zx) ?_
  exact VG.RelCT.seq (nwStages_rel pg) ((nbStages_rel pg).mono (fun _ _ h => h) fun _ _ _ => trivial)

/-! ## `finishX` -/

/-- A header word's value is a word. -/
theorem KS.vlt {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : d ∈ ls) : V d < 2 ^ 32 := by
  rw [← h.sl d hd]; exact (s.mem.readW _ 32).isLt

abbrev fF1 : Prog isa := .seq (.block (arrPtr wid .esi sqZ .edx ++ bytesB wid .edx ++ [.mov .ecx (.imm 0)]))
  (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne)
abbrev fF2 : Prog isa := .block (flagZero ++ [.mov .eax (.mem (sc sStg)), .store (sc sOk5) .eax])
abbrev fF3 : Prog isa := .block [.mov .ebx (.imm 0)]
abbrev fF4 : Prog isa := half wid sqD
abbrev fWB : Prog isa := .block [.mov .eax (.mem (sc sKw)), .shift .shr .eax 1, .mov .edx (.mem (sc sC4)),
  .shift .shr .edx 2, .alu .and .eax (.reg .edx), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax),
  .alu .add .eax (.imm 1), .store (sc sStg) .eax]
abbrev fWBody : Prog isa := seqs [fWB, moveH wid sqD wT true false, sel wid sqD sqD wT sStg]
abbrev fF5 : Prog isa := wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) fWBody
abbrev fF6 : Prog isa := .block [.mov .eax (.mem (sc sKw)), .alu .and .eax (.imm 1), .alu .add .eax (.reg .eax),
  .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .edx (.mem (sc sZb)),
  .shift .shr .edx 1, .alu .add .eax (.reg .edx), .store (sc sZb) .eax]
abbrev fBB : Prog isa := .block [.mov .eax (.mem (sc sZb)), .alu .and .eax (.mem (sc sB)), .alu .cmp .eax (.imm 1),
  .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1), .store (sc sStg) .eax]
abbrev fF7 : Prog isa := bitStagesL 16 1 (.seq fBB (downBitsSelH sqD))
abbrev fF8 : Prog isa := .block (arrPtr wid .esi sqD .edx ++ [.mov .eax (.mem (at_ .esi 0)),
  .alu .sub .eax (.mem (sc sZf)), .store (at_ .esi 0) .eax])
abbrev fF9 : Prog isa := copy nar aY (2 * sqD)

theorem finishX_eq : finishX = seqs [fF1, fF2, fF3, fF4, fF5, fF6, fF7, fF8, fF9] := rfl

theorem c_f12 : OkK [] (.seq fF1 fF2) := ⟨_, by taint_decide⟩
theorem c_f34 : OkK [] (.seq fF3 fF4) := ⟨_, by taint_decide⟩
theorem c_fwInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * 2 ^ 7))), .store (sc sC4) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_fwLim : OkK [sC4] (.block (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
    ([.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)] : List Instr))) := ⟨_, by taint_decide⟩
theorem c_fWBody : OkK [sC4] fWBody := ⟨_, by taint_decide⟩
theorem c_f6 : OkK [] fF6 := ⟨_, by taint_decide⟩
theorem c_fbInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (2 ^ 4))), .store (sc sB) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_fbHalf : OkK [sB] (.block (halfB 0)) := ⟨_, by taint_decide⟩
theorem c_fBB : OkK [] fBB := ⟨_, by taint_decide⟩
theorem c_cpD : OkK [] (copy wid wT sqD) := ⟨_, by taint_decide⟩
theorem c_hfT : OkK [] (.seq (.block [.mov .ebx (.imm 0)]) (half wid wT)) := ⟨_, by taint_decide⟩
theorem c_selD : OkK [] (sel wid sqD sqD wT sStg) := ⟨_, by taint_decide⟩
theorem c_f89 : OkK [] (.seq fF8 fF9) := ⟨_, by taint_decide⟩

/-- `finishX`'s frame: `D` in `sqD`, the header words `ls`. -/
abbrev FQ (a : Nat) (ls : List Nat) (F : (Nat → Nat) → Prop) : Geo → State → Prop :=
  QW a [aD, aZero] [sqD] ls fun _ V => F V

/-- `finishX`'s word stages, related. -/
theorem fwStages_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (FQ a lsN (fun _ => True) g)) fF5 (Both (FQ a (sC4 :: lsN) (fun _ => True) g)) := by
  have e : fF5 = wordStagesL (2 ^ 7) (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) fWBody := rfl
  rw [e]
  refine relWordStagesL (lim := 4 * wq a) (S := FQ a lsN fun _ => True) (Fin := FQ a (sC4 :: lsN) fun _ => True)
    (fun g' j => FQ a (sC4 :: lsN) (fun V => V sC4 = 4 * 2 ^ j) g')
    (fun g' j => FQ a (sC4 :: lsN) (fun V => V sC4 = 4 * 2 ^ j) g') (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ _ h => h.p0 pg)
    (fun _ h => h.onView) (fun _ _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨_, _, _, _, _, k, _⟩ => k.ws) ?_ ?_ ?_ ?_ (fun _ _ _ _ h _ => h) ?_ ?_ ?_ c_fwInit c_fwLim c_xsHalf
  · rintro g' s u ⟨ga, s0, A, AW, V, h, _⟩ k hs K
    exact ⟨ga, s0, A, AW, _, h.slot1 k (by decide) (K.mono (by decide)) hs, upd_self _ _ _⟩
  · rintro g' j u - ⟨_, _, _, _, _, h, f⟩
    exact ⟨h.ws, by rw [h.sl _ (by simp), f]⟩
  · rintro g' j u - ⟨ga, _, _, _, _, h, _⟩ is Q k
    have w4 : 4 * wq a < 2 ^ 32 := by simp only [wq]; have := ga.2.2.1; omega
    exact VG.Proof.Rsa.X86.WordRt.width4_ok (h.mlen ga.1 ga.2.2.1) (r := .eax)
      fun u' K m e => k u' (K.mono (by decide)) m (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4])
  · rintro g' j u v - ⟨ga, s0, A, AW, V, h, f⟩ K m
    exact ⟨ga, s0, A, AW, V, h.of_rest K (fun x hx => hx) m, f⟩
  · rintro g' j u - ⟨_, _, _, _, _, h, f⟩
    exact ⟨h.ws, by rw [h.sl _ (by simp), f]⟩
  · rintro g' j u v hj ⟨ga, s0, A, AW, V, h, _⟩ k e K
    have h' := (h.slot1 k (by decide) K e).mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
      (fun _ he => ⟨List.mem_cons_of_mem _ he, rfl⟩)
    refine ⟨fun hj0 => ⟨ga, s0, A, AW, _, h', ?_⟩, fun _ => ⟨ga, s0, A, AW, _, h', trivial⟩⟩
    show upd V _ _ _ = _
    rw [upd_self]
    have : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  · intro j _ hl
    refine leafQ pg (fun _ => 4 * 2 ^ j) (by decide)
      (fun _ V f d hd => by simp only [List.mem_singleton] at hd; subst hd; exact f) ?_ c_fWBody
    rintro g' u ⟨ga, s0, A, AW, V, h, f⟩
    have cW : 2 ^ j < g'.W := by
      have := ga.2.1; simp only [Geo.W, Geo.w, VG.Impl.Rsa.X86.Recover.wide, VG.Impl.Rsa.X86.Recover.width] at this ⊢
      omega
    simp only [seqs]
    refine WP.seq (WP.mono (h.wordFlag (by simp) (by simp) (h.vlt (by simp)) (h.vlt (by simp)))
      fun u₁ ⟨h₁, _⟩ => ?_)
    refine WP.seq (WP.mono (h₁.moveDown_W (o := wT) (a := sqD) (c := 2 ^ j) (by decide) (by simp) (by decide) cW
      (by simp) (by rw [upd_ne _ _ (by decide)]; omega) (by decide)) fun u₂ ⟨h₂, _, _⟩ => ?_)
    refine WP.mono (h₂.sel_W (o := sqD) (a := sqD) (b := wT) (sl := sStg) (by decide) (by simp) (by simp)
      (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun u₃ ⟨h₃, _⟩ => ?_
    refine ⟨ga, s0, A, _, _, h₃.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), ?_⟩
    show upd V sStg _ sC4 = _
    rw [upd_ne _ _ (show sC4 ≠ sStg by decide)]; exact f

/-- `finishX`'s bit stage of `2^j` bits, related. -/
theorem fbBody_rel {g : Geo} (pg : PubG g) {a j : Nat} (hj : 2 ^ j < 32) :
    RelCT isa (Both (FQ a (sB :: lsN) (fun V => V sB = 2 ^ j) g)) (.seq fBB (downBitsSelH sqD))
      (Both (FQ a (sB :: lsN) (fun V => V sB = 2 ^ j) g)) := by
  have hb : 0 < 2 ^ j := Nat.two_pow_pos j
  refine VG.RelCT.seq (leafQ (Q := QB a (2 ^ j) [aD, aZero] [sqD] (sStg :: sB :: lsN)) pg (fun _ => 0) (ds := [])
    (by simp) (by simp) (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ => WP.mono (h.bitFlag (by simp) (by simp)
      (h.vlt (by simp)) (h.vlt (by simp))) fun _ ⟨h', _⟩ => ⟨ga, s0, A, AW, _, h',
        by rw [upd_self]; split <;> decide, by rw [upd_ne _ _ (by decide)]; exact f⟩) c_fBB) ?_
  show RelCT isa _ (.seq (copy wid wT sqD) (.seq (timesH (.seq (.block [.mov .ebx (.imm 0)]) (half wid wT)))
    (sel wid sqD sqD wT sStg))) _
  refine VG.RelCT.seq (leafQ (Q := QB a (2 ^ j) [aD, aZero] [wT, sqD] (sStg :: sB :: lsN)) pg (fun _ => 0)
    (ds := []) (by simp) (by simp) (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ => WP.mono (h.copy_W (o := wT) (a := sqD)
      (by decide) (by simp) (by decide) (by decide)) fun _ ⟨h', _⟩ => ⟨ga, s0, A, _, V, h', f⟩) c_cpD) ?_
  refine VG.RelCT.seq (sqTimes pg hb (by omega) (by simp) c_hfT fun g' s0 A AW V s h => by
    refine WP.seq (wp_movS (v := 0) rfl fun t₁ U _ => WP.block_nil ?_)
    have P₁ := h.of_rest U.keeps (by decide) U.mem
    exact WP.mono (P₁.half_W (j := wT) (by simp) (by rw [U.gpr]; rfl) (by decide)) fun _ ⟨hv, _⟩ =>
      ⟨A, _, hv.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
        (fun _ hd => ⟨hd, rfl⟩)⟩) ?_
  exact leafQ pg (fun _ => 0) (ds := []) (by simp) (by simp)
    (fun g' s ⟨ga, s0, A, AW, V, h, f⟩ => WP.mono (h.sel_W (o := sqD) (a := sqD) (b := wT) (sl := sStg) (by decide)
      (by simp) (by simp) (by simp) f.1 (.inr (by decide)) (by decide)) fun _ ⟨h', _⟩ =>
        ⟨ga, s0, A, _, V, h'.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨by simp at hj ⊢; omega, rfl⟩)
          (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), f.2⟩) c_selD

/-- `finishX`'s bit stages, related. -/
theorem fbStages_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (FQ a lsN (fun _ => True) g)) fF7 (Both (FQ a (sB :: lsN) (fun _ => True) g)) := by
  have e : fF7 = bitStagesL (2 ^ 4) (2 ^ 0) (.seq fBB (downBitsSelH sqD)) := rfl
  rw [e]
  refine relBitStagesL (S := FQ a lsN fun _ => True) (Fin := FQ a (sB :: lsN) fun _ => True)
    (fun g' j => FQ a (sB :: lsN) (fun V => V sB = 2 ^ j) g')
    (fun g' j => FQ a (sB :: lsN) (fun V => V sB = 2 ^ j) g') (by decide) (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨_, _, _, _, _, k, _⟩ => k.ws) ?_ ?_ ?_ ?_ c_fbInit c_fbHalf
  · rintro g' s u ⟨ga, s0, A, AW, V, h, _⟩ k hs K
    exact ⟨ga, s0, A, AW, _, h.slot1 k (by decide) (K.mono (by decide)) hs, upd_self _ _ _⟩
  · rintro g' j u - - ⟨_, _, _, _, _, h, f⟩
    exact ⟨h.ws, by rw [h.sl _ (by simp), f]⟩
  · rintro g' j u v - _ ⟨ga, s0, A, AW, V, h, _⟩ k e K
    have h' := (h.slot1 k (by decide) K e).mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
      (fun _ he => ⟨List.mem_cons_of_mem _ he, rfl⟩)
    refine ⟨fun hj0 => ⟨ga, s0, A, AW, _, h', ?_⟩, fun _ => ⟨ga, s0, A, AW, _, h', trivial⟩⟩
    show upd V _ _ _ = _
    rw [upd_self]
    have : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  · intro j _ hj
    have := Nat.pow_le_pow_right (n := 2) (by decide) hj
    exact fbBody_rel pg (by simp at this; omega)

/-- `finishX`, related: its run's values aside. -/
theorem finishX_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (QW a [aD, aZero] [wR, sqD] lsN (fun _ _ => True) g)) finishX (fun _ _ => True) := by
  rw [finishX_eq]
  refine relSeqs (x := fF1) (xs := [fF2]) (y := fF3) (ys := [fF4, fF5, fF6, fF7, fF8, fF9])
    (R := Both (FQ a lsN (fun _ => True) g)) (leafQ pg (fun _ => 0) (ds := []) (by simp) (by simp) ?_ c_f12) ?_
  · rintro g' s ⟨ga, s0, A, AW, V, h, _⟩
    refine WP.seq (WP.mono (h.orAll (j := wR) (by simp)) fun u₁ ⟨h₁, _, _⟩ => ?_)
    refine WP.block_append (WP.mono h₁.flagZero fun u₂ ⟨h₂, _⟩ => ?_)
    refine wp_movS (h₂.readSlot (d := sStg) (by simp)) fun u₃ U₃ _ => ?_
    have h₃ := h₂.of_rest U₃.keeps (by decide) U₃.mem
    refine WP.mono (h₃.storeSlot (d := sOk5) (by decide) .eax) fun u₄ ⟨h₄, _, _⟩ => ⟨ga, s0, A, AW, _,
      h₄.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨by simp at hj ⊢; omega, rfl⟩)
        (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), rfl⟩), trivial⟩
  refine relSeqs (x := fF3) (xs := [fF4]) (y := fF5) (ys := [fF6, fF7, fF8, fF9])
    (R := Both (FQ a lsN (fun _ => True) g)) (leafQ pg (fun _ => 0) (ds := []) (by simp) (by simp) ?_ c_f34) ?_
  · rintro g' s ⟨ga, s0, A, AW, V, h, _⟩
    refine WP.seq (wp_movS (v := 0) rfl fun u U _ => WP.block_nil ?_)
    have hu := h.of_rest U.keeps (by decide) U.mem
    exact WP.mono (hu.half_W (j := sqD) (by simp) (by rw [U.gpr]; rfl) (by decide)) fun _ ⟨h', _⟩ =>
      ⟨ga, s0, A, _, V, h'.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨by simp at hj ⊢; omega, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), trivial⟩
  refine VG.RelCT.seq (fwStages_rel pg) (VG.RelCT.seq (leafQ (Q := FQ a lsN fun _ => True) pg (fun _ => 0)
    (ds := []) (by simp) (by simp) ?_ c_f6) (VG.RelCT.seq (fbStages_rel pg) ?_))
  · rintro g' s ⟨ga, s0, A, AW, V, h, _⟩
    exact WP.mono (h.zbBlock (by simp) (by simp) (h.vlt (by simp)) (h.vlt (by simp))) fun _ h' =>
      ⟨ga, s0, A, AW, _, h'.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
        (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), rfl⟩), trivial⟩
  exact (leafQ (Q := fun _ _ => True) pg (fun _ => 0) (ds := []) (by simp) (by simp)
    (fun g' s ⟨_, _, _, _, _, h, _⟩ => WP.seq (WP.mono (h.subLow_w (j := sqD) (by simp) (by simp) (by decide))
      fun _ ⟨_, hu⟩ => WP.mono ((hu.view (j := sqD) (by simp)).copy_w (o := aY) (a := 2 * sqD) (by decide)
        (by simp) (by decide) (by decide)) fun _ _ => trivial)) c_f89).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## `sqrt` -/

/-- A frame of the square root, its facts `F` on the narrow arrays too. -/
def QA (a : Nat) (live liveW ls : List Nat) (F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop) (g : Geo)
    (s : State) : Prop :=
  SqG g a ∧ ∃ s0 A AW V, KS g s0 A live AW liveW V ls s ∧ F A AW V

section
variable {a : Nat} {live liveW ls : List Nat} {F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop}
  {g : Geo} {s : State}

theorem QA.onView (h : QA a live liveW ls F g s) : QA a live liveW ls F g.vw (view s g.B g.Z) :=
  let ⟨ga, _, A, AW, V, k, f⟩ := h
  ⟨ga, _, A, AW, V, k.onView, f⟩

theorem QA.p0 (pg : PubG g) (h : QA a live liveW ls F g s) : P0 g s :=
  let ⟨_, _, _, _, _, k, _⟩ := h
  k.pre0 pg

end

/-- A leaf, no header word public, from a frame of the square root. -/
theorem leafA {a : Nat} {g : Geo} (pg : PubG g) {live liveW ls : List Nat}
    {F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop} {Q : Geo → State → Prop} {c : Prog isa}
    (hf : ∀ g' s, QA a live liveW ls F g' s → WP isa c s (Q g')) (h : OkK [] c) :
    RelCT isa (Both (QA a live liveW ls F g)) c (Both (Q g)) :=
  leafP (fun _ => 0) (by simp) (fun _ h => h.p0 pg) (fun _ h => h.onView) (by simp) hf h

/-- The normalization's facts: `X = (X₀ + [X₀ = 0]) 4^(16 K + z / 2)`. -/
def NF (V0 : Nat → Nat) (a X X₀ : Nat) : Prop :=
  V0 sZf = (if X₀ = 0 then 1 else 0) ∧ X = (X₀ + V0 sZf) * 4 ^ (16 * V0 sKw + V0 sZb / 2) ∧
    V0 sKw < 2 * wq a ∧ V0 sZb % 2 = 0 ∧ V0 sZb ≤ 30

/-- Before `sqrt`. -/
abbrev SM (a : Nat) : Geo → State → Prop := QA a [aD, aZero] [wR] sqSlotsW fun A _ _ => A aZero = 0

/-- After `normX`. -/
abbrev SN (a : Nat) : Geo → State → Prop := QA a [aD, aZero] [wR] lsN fun A AW V =>
  A aZero = 0 ∧ ∃ X₀, NF V a (AW wR) X₀ ∧ AW wR < 2 ^ (64 * wq a) ∧ 2 ^ 30 * 2 ^ (64 * wq a - 32) ≤ AW wR

/-- After `firstX`. -/
abbrev SFX (a : Nat) : Geo → State → Prop := QA a [aD, aZero] [wR, sqD]
  (VG.Impl.Rsa.X86.WordModRt.oD :: VG.Impl.Rsa.X86.WordModRt.oV :: lsN) fun A AW V =>
  A aZero = 0 ∧ ∃ V0 X X₀ s r, (∀ d ∈ lsN, V d = V0 d) ∧ SqR a X (wq a - 1) s r AW V ∧ NF V0 a X X₀

/-- Before the digit step with `j` in `sCt` (`SqI`), and the normalization's facts. -/
abbrev SL (a j : Nat) : Geo → State → Prop := QA a [aD, aZero] [wR, sqD]
  (sCt :: VG.Impl.Rsa.X86.WordModRt.oD :: VG.Impl.Rsa.X86.WordModRt.oV :: lsN) fun A AW V =>
  A aZero = 0 ∧ V sCt = j ∧ ∃ V0 X X₀ s r, (∀ d ∈ lsN, V d = V0 d) ∧ SqR a X j s r AW V ∧ NF V0 a X X₀

/-- After `sqrt`. -/
abbrev SE (a : Nat) : Geo → State → Prop :=
  QA a [aY, aD, aZero] [] (sOk5 :: sqSlotsW) fun A _ _ => A aZero = 0

theorem SL.sqI {a j : Nat} {g : Geo} {u : State} (h : SL a j g u) :
    SqG g a ∧ ∃ s0 A V0 X X₀, SqI g s0 A V0 a X j u ∧ A aZero = 0 ∧ NF V0 a X X₀ :=
  let ⟨ga, s0, A, AW, V, k, z, hC, V0, X, X₀, s, r, hl, hR, nf⟩ := h
  ⟨ga, s0, A, V0, X, X₀, ⟨AW, V, s, r, k, hl, hC, hR⟩, z, nf⟩

theorem SqI.sl {a j : Nat} {g : Geo} {s0 u : State} {A V0 : Nat → Nat} {X X₀ : Nat} (ga : SqG g a)
    (h : SqI g s0 A V0 a X j u) (z : A aZero = 0) (nf : NF V0 a X X₀) : SL a j g u :=
  let ⟨AW, V, s, r, k, hl, hC, hR⟩ := h
  ⟨ga, s0, A, AW, V, k, z, hC, V0, X, X₀, s, r, hl, hR, nf⟩

theorem c_first : OkK [] firstX := ⟨_, by taint_decide⟩
theorem c_cnt : OkK [] (.block (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
    ([.shift .shr .eax 2, .alu .sub .eax (.imm 1), .store (sc sCt) .eax] : List Instr))) := ⟨_, by taint_decide⟩
theorem c_nil : OkK [] (.block []) := ⟨_, by taint_decide⟩

/-- `sCt := W' - 1`, from `firstX`'s end. -/
theorem cnt_w {a : Nat} {g : Geo} {u : State} (h : SFX a g u) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
      ([.shift .shr .eax 2, .alu .sub .eax (.imm 1), .store (sc sCt) .eax] : List Instr))) u fun v =>
      SL a (wq a - 1) g v ∧ v.zf = some (decide (wq a - 1 = 0)) := by
  obtain ⟨ga, s0, A, AW2, V2, h2, z, V0, X, X₀, s₀, r₀, e2, hR2, nf⟩ := h
  have hw1 : 1 ≤ wq a := by simp only [wq]; have := ga.2.2.2; omega
  have ha1 := ga.2.2.1
  refine VG.Proof.Rsa.X86.WordRt.width4_ok (h2.mlen ga.1 ha1) fun u3 K3 m3 e3 => ?_
  have h3 := h2.of_rest K3 (by decide) m3
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u4 U4 => ?_
  refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun u5 U5 z5 => ?_
  have h5 := (h3.of_rest U4.keeps (by decide) U4.mem).of_rest U5.keeps (by decide) U5.mem
  have v5 : (u5.gpr .eax).toNat = wq a - 1 := by
    rw [U5.gpr, U4.gpr, e3, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    simp only [wq] at hw1 ⊢; omega
  refine WP.mono (h5.storeSlot (d := sCt) (by decide) .eax) fun u6 ⟨h6, zf6, _⟩ => ?_
  rw [v5] at h6
  refine ⟨⟨ga, s0, A, AW2, _, h6, z, upd_self _ _ _, V0, X, X₀, s₀, r₀, ?_, ?_, nf⟩, ?_⟩
  · intro d hd
    have : d ≠ sCt := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [upd_ne _ _ this, e2 d hd]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hR2
    have n1 : VG.Impl.Rsa.X86.WordModRt.oD ≠ sCt := by decide
    have n2 : VG.Impl.Rsa.X86.WordModRt.oV ≠ sCt := by decide
    exact ⟨a1, a2, a3, a4, by rw [upd_ne _ _ n1]; exact a5, by rw [upd_ne _ _ n1]; exact a6, a7,
      by rw [upd_ne _ _ n2, upd_ne _ _ n1]; exact a8⟩
  · rw [zf6, z5, ← U5.gpr]; congr 1
    by_cases e : wq a - 1 = 0
    · simp only [e, decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [v5, e]; rfl
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c; have := congrArg BitVec.toNat c; rw [v5] at this; exact e this

/-- The digit steps, related. -/
theorem digits_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (fun s t => (SL a (wq a - 1) g s ∧ s.zf = some (decide (wq a - 1 = 0))) ∧
      (SL a (wq a - 1) g t ∧ t.zf = some (decide (wq a - 1 = 0))))
      (.ite .e (.block []) (.loop stepX .ne)) (Both (SL a 0 g)) := by
  refine VG.RelCT.ite (fun s t ⟨⟨_, hs⟩, ⟨_, ht⟩⟩ => by simp only [eval, hs, ht]) ?_ ?_
  · refine (leafA (Q := SL a 0) pg (fun _ _ h => WP.block_nil h) c_nil).mono (fun s t ⟨⟨⟨hs, zs⟩, ⟨ht, _⟩⟩, c⟩ => ?_)
      (fun _ _ h => h)
    have e : wq a - 1 = 0 := by simpa [eval, zs] using c
    rw [e] at hs ht
    exact ⟨hs, ht⟩
  · intro s t tr ur sf tf ⟨⟨⟨hs, zs⟩, ⟨ht, _⟩⟩, c⟩ es et
    have e : wq a - 1 ≠ 0 := by simpa [eval, zs] using c
    let L : Nat → State → Prop := fun k u => SL a (wq a - 1 - k) g u
    have R := relLoop (body := stepX) (c := .ne) L (K := wq a - 1) (by omega) (fun k hk => ?_) (fun k u hk hu => ?_)
    · obtain ⟨tr', h⟩ := R s t tr ur sf tf ⟨by simpa [L] using hs, by simpa [L] using ht⟩ es et
      refine ⟨tr', ?_⟩
      have h' : L (wq a - 1) sf ∧ L (wq a - 1) tf := h
      simp only [L, Nat.sub_self] at h'
      exact h'
    · refine (stepX_rel (g := g) (a := a) (j := wq a - 1 - k)).mono (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩) (fun _ _ h => h)
      · obtain ⟨ga, s0, A, V0, X, X₀, hI, _⟩ := (show SL a (wq a - 1 - k) g s from hs).sqI
        exact ⟨ga, by omega, by omega, (show SL a (wq a - 1 - k) g s from hs).p0 pg, s0, A, V0, X, hI⟩
      · obtain ⟨ga, s0, A, V0, X, X₀, hI, _⟩ := (show SL a (wq a - 1 - k) g t from ht).sqI
        exact ⟨ga, by omega, by omega, (show SL a (wq a - 1 - k) g t from ht).p0 pg, s0, A, V0, X, hI⟩
    · obtain ⟨ga, s0, A, V0, X, X₀, hI, z, nf⟩ := (show SL a (wq a - 1 - k) g u from hu).sqI
      refine WP.mono (stepX_ok hI ga.1 ga.2.2.1 ga.2.1 (by omega) (by omega)) fun v ⟨zv, I⟩ => ⟨?_, ?_⟩
      · show SL a (wq a - 1 - (k + 1)) g v
        rw [show wq a - 1 - (k + 1) = wq a - 1 - k - 1 by omega]; exact I.sl ga z nf
      · have : (wq a - 1 - k - 1 = 0) ↔ ¬ (k + 1 < wq a - 1) := by omega
        simp only [eval, zv, Option.map_some]
        congr 1
        by_cases h1 : k + 1 < wq a - 1 <;> simp [h1] <;> omega

theorem SM.n0 {a : Nat} {g : Geo} {s : State} (h : SM a g s) : N0 a g s :=
  let ⟨ga, s0, A, AW, V, k, _⟩ := h
  ⟨ga, s0, A, AW, V, k, trivial⟩

/-- The square root, related: from two runs' radicands to their roots. -/
theorem sqrt_rel {g : Geo} (pg : PubG g) {a : Nat} :
    RelCT isa (Both (SM a g)) sqrt (Both (SE a g)) := by
  have e : sqrt = .seq normX (.seq firstX (.seq (.block (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
      ([.shift .shr .eax 2, .alu .sub .eax (.imm 1), .store (sc sCt) .eax] : List Instr)))
      (.seq (.ite .e (.block []) (.loop stepX .ne)) finishX))) := rfl
  rw [e]
  refine VG.RelCT.seq (relAug ((normX_rel pg).mono (fun s t ⟨hs, ht⟩ => ⟨hs.n0, ht.n0⟩) (fun _ _ h => h))
    (S := SN a g) fun s ⟨ga, s0, A, AW, V, h, z⟩ => ?_) ?_
  · exact WP.mono (normX_ok h rfl ga.1 ga.2.2.1 ga.2.2.2 ga.2.1)
      fun _ ⟨AW', V', h', _, hz, hval, hlt, hge, hK, hev, hzb⟩ =>
        ⟨ga, s0, A, AW', V', h', z, _, ⟨hz, hval, hK, hev, hzb⟩, hlt, hge⟩
  refine VG.RelCT.seq (leafA (Q := SFX a) pg (fun g' s ⟨ga, s0, A, AW, V, h, z, X₀, nf, hlt, hge⟩ =>
    WP.mono (firstX_ok h rfl ga.1 ga.2.2.1 ga.2.2.2 ga.2.1 hlt hge) fun _ ⟨AW', V', s₀, r₀, h', e', hR⟩ =>
      ⟨ga, s0, A, AW', V', h', z, V, AW wR, X₀, s₀, r₀, e', hR, nf⟩) c_first) ?_
  refine VG.RelCT.seq (leafA (Q := fun g' v => SL a (wq a - 1) g' v ∧ v.zf = some (decide (wq a - 1 = 0))) pg
    (fun _ _ h => cnt_w h) c_cnt) ?_
  refine VG.RelCT.seq (digits_rel pg) ?_
  refine relAug ((finishX_rel pg (a := a)).mono (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩) (fun _ _ h => h)) ?_
  · obtain ⟨ga, s0, A, AW, V, k, _⟩ := hs
    exact ⟨ga, s0, A, AW, V, k.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)), rfl⟩), trivial⟩
  · obtain ⟨ga, s0, A, AW, V, k, _⟩ := ht
    exact ⟨ga, s0, A, AW, V, k.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)), rfl⟩), trivial⟩
  · intro u hu
    obtain ⟨ga, s0, A, V0, X, X₀, hI, z, hz, hXe, hK, hzb, hzb'⟩ := hu.sqI
    exact WP.mono (finishX_ok hI z ga.1 ga.2.2.1 ga.2.2.2 ga.2.1 hz hXe hK hzb hzb')
      fun _ ⟨A', AW', h', _, _, z'⟩ => ⟨ga, s0, A', AW', _, h', z'⟩

/-- `sqrt`, between `det`'s stages. -/
theorem sqrt_relCT {g : Geo} (pg : PubG g) (a : Nat) (ha : g.args nl = BitVec.ofNat 32 a) (ha0 : 1 ≤ a)
    (ha1 : a ≤ 1024) (haw : wq a ≤ g.w) :
    RelCT isa (RA (M41 g) (M41 g)) sqrt (RA (SR1 g) (SR1 g)) := by
  have ga : SqG g a := ⟨ha, haw, ha1, ha0⟩
  refine (sqrt_rel pg (a := a)).mono (fun s t ⟨_, ⟨s0, A, AW, V, h, z⟩, ⟨t0, B, BW, W, k, y⟩⟩ =>
    ⟨⟨ga, s0, A, AW, V, h, z⟩, ⟨ga, t0, B, BW, W, k, y⟩⟩) fun s t ⟨⟨_, s0, A, AW, V, h, z⟩, ⟨_, t0, B, BW, W, k, y⟩⟩ =>
      RA.of pg (P := SR1 g) (fun _ ⟨_, _, _, _, h, _⟩ => h.stage) ⟨s0, A, AW, V, h, z⟩ ⟨t0, B, BW, W, k, y⟩

end VG.Proof.Rsa.X86.Recover
