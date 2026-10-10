import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg

/-!
# Ed448's point functions on x86-64: what they compute

Untrusted: everything here is checked by Lean. A function running the field
program `ops` (`fn ops`) changes the slots as `evalOps ops` (`fieldCode_ok`)
and nothing else but the registers `clob` (`Keep`): `saves` changes only
`xmm0`–`xmm4`, and `restores` only registers of `clob` (`fn_ok`). Its bytes
change only in the slots its operations write and in the product's words
(`fieldCode_frame`), and it restores `rbp` and `r12`–`r15`, which
`KeepReg.keeps` follows through `xmm0`–`xmm4` (`fn_regs`). The doubling's
values are RFC 8032's (`doubleOps_eval`), the affine addition's `addOps`'s
for a second point with `Z = 1` (`addAffineOps_eval`).
-/

namespace VG.Proof.Ed448.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk clob ofs Outside Outside2 E_update slot_lt)
open VG.Impl.X448.X86_64 (slot ACC)

private theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
private theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
private theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
private theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl

/-- The registers the functions restore. -/
abbrev keptRegs : List Reg := kept.map Prod.fst

theorem saves_ok (s : State) :
    WP isa (.block saves) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [saves, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, Option.some.injEq, exists_eq_left', setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem restores_ok (s : State) :
    WP isa (.block restores) s fun t => (∀ r, r ∉ keptRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [restores, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2]

/-! ## The bytes a field program writes -/

/-- The byte at `x` is outside the slot that `op` writes. -/
def OutOf (base : Addr) (x : Addr) (op : FOp) : Prop :=
  ofs base x < slot (fopDest op) ∨ slot (fopDest op) + 56 ≤ ofs base x

theorem slot_idx' {n : Nat} (h : n < 22) : slot (idx n).val = slot n := by
  simp only [idx, Nat.mod_eq_of_lt h]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem fop_frame {s : State} {base : Addr} (hs : Scr s base) (op : FOp) (hv : fopValid op) :
    WP isa (.block (fopCode fld op)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOp op (E s.mem base) ∧
        ∀ x, OutOf base x op → (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) → t.mem x = s.mem x := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, OutOf, fopDest, ← slot_idx' h1, ← slot_idx' h2, ← slot_idx' h3]
    exact WP.mono (hf.mul hs (slot_lt _) (slot_lt _) (slot_lt _)) fun _ ⟨h, e⟩ =>
      ⟨h.keep, by rw [E_update h.mem, e]; rfl, fun x h₁ h₂ => h.mem x h₁ h₂⟩
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [fopCode, OutOf, fopDest, ← slot_idx' h1, ← slot_idx' h2]
    exact WP.mono (hf.sqr hs (slot_lt _) (slot_lt _)) fun _ ⟨h, e⟩ =>
      ⟨h.keep, by rw [E_update h.mem, e]; rfl, fun x h₁ h₂ => h.mem x h₁ h₂⟩
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, OutOf, fopDest, ← slot_idx' h1, ← slot_idx' h2, ← slot_idx' h3]
    exact WP.mono (Proof.X448.X86_64.add_ok hs (slot_lt _) (slot_lt _) (slot_lt _)) fun _ ⟨h, e⟩ =>
      ⟨h.keep, by rw [E_update h.mem, e]; rfl, fun x h₁ h₂ => h.mem x h₁ h₂⟩
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, OutOf, fopDest, ← slot_idx' h1, ← slot_idx' h2, ← slot_idx' h3]
    exact WP.mono (Proof.X448.X86_64.sub_ok hs (slot_lt _) (slot_lt _) (slot_lt _)) fun _ ⟨h, e⟩ =>
      ⟨h.keep, by rw [E_update h.mem, e]; rfl, fun x h₁ h₂ => h.mem x h₁ h₂⟩

include hf in
/-- A field program changes the slots as `evalOps`, and only the bytes of the slots it writes and
of the product's words. -/
theorem fieldCode_frame (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps ops (E s.mem base) ∧
        ∀ x, (∀ op ∈ ops, OutOf base x op) → (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) →
          t.mem x = s.mem x := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ _ => rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_frame hf hs op (hv op List.mem_cons_self)) fun t ⟨ht, et, ft⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (ht.scr hs))
      fun u ⟨hu, eu, fu⟩ => ⟨ht.trans hu, by rw [eu, et, evalOps, evalOps, List.foldl_cons], fun x hx ha => by
        rw [fu x (fun o h => hx o (List.mem_cons_of_mem _ h)) ha, ft x (hx op List.mem_cons_self) ha]⟩

/-- A function running the field program `ops`: the registers but `clob` kept, the slots'
values `evalOps ops` of theirs, and memory changed only at the program's results and the
product's words. -/
theorem fn_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) :
    WP isa (fn ops) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps ops (E s.mem base) ∧
        ∀ x, (∀ op ∈ ops, OutOf base x op) → (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) →
          t.mem x = s.mem x := by
  simp only [fn, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_frame Proof.X448.X86_64.baseline_ok ops hv hs₁) fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
  refine WP.mono (restores_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁], ?_⟩, by rw [m₃, e₂, m₁],
    fun x hx ha => by rw [m₃, f₂ x hx ha, m₁]⟩
  · have hk : r ∉ keptRegs := fun h => hr (by
      revert h; simp only [keptRegs, kept, clob, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
    rw [g₃ r hk, k₂.gpr r hr, g₁]
  · intro x hx
    rw [m₃, k₂.mem x hx, m₁]

/-- `fn_ok`, with the registers the function restores kept too (`KeepReg.keeps`). -/
theorem fn_regs (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn ops) = true) {s : State} {base : Addr}
    (hs : Scr s base) :
    ∃ t s', Exec isa (fn ops) s t s' ∧ (∀ r, (r ∉ clob ∨ r ∈ keptRegs) → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ E s'.mem base = evalOps ops (E s.mem base) ∧
      ∀ x, (∀ op ∈ ops, OutOf base x op) → (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) →
        s'.mem x = s.mem x := by
  obtain ⟨t, s', he, k, e, f⟩ := fn_ok ops hv hs
  exact ⟨t, s', he, fun r hr => hr.elim (k.gpr r) fun hm => Exec.gpr_keeps (hk r hm) he, k.rd, k.wr, e, f⟩

/-! ## The programs' values -/

theorem addAffineOps_valid : ∀ op ∈ addAffineOps, fopValid op := by decide

/-- `addWith` of a point with `Z = 1`, with `Z₁` for `Z₁ · 1`. -/
def addAffineWith (dd : Spec.X448.Fe) (p : Spec.Ed448.Point) (x y : Spec.X448.Fe) : Spec.Ed448.Point :=
  let b := p.Z * p.Z
  let c := p.X * x
  let d' := p.Y * y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (x + y)
  ⟨p.Z * f * (h - c - d'), p.Z * g * (d' - c), f * g⟩

theorem addWith_affine (dd : Spec.X448.Fe) (p : Spec.Ed448.Point) (x y : Spec.X448.Fe) :
    addWith dd p ⟨x, y, 1⟩ = addAffineWith dd p x y := by
  simp only [addWith, addAffineWith, Fin.mul_one]

theorem addAffineOps_eval (e : Env) :
    pt (evalOps addAffineOps e) 3 4 5 = addWith (e 11) (pt e 0 1 2) ⟨e 8, e 9, 1⟩ := by
  rw [addWith_affine]; rfl

theorem double_eq (p : Spec.Ed448.Point) : double p = Spec.Ed448.Point56.pointDouble p := rfl

end VG.Proof.Ed448.X86_64.Point64

namespace VG.Proof.Ed448.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr E Keep)

/-- What the callers need of their point operations: each changes the slots as its field
program does, and nothing else but the registers `clob` and the memory in `[64, 1648)`. -/
structure PointOk (P : Ops) : Prop where
  dbl : ∀ {s : State} {base : Addr}, Scr s base →
    WP isa P.dbl s fun t => Keep base s t ∧ E t.mem base = evalOps doubleOps (E s.mem base)
  add : ∀ {s : State} {base : Addr}, Scr s base →
    WP isa P.add s fun t => Keep base s t ∧ E t.mem base = evalOps addAffineOps (E s.mem base)

/-- The functions' code, as the calls run it. -/
theorem bodies_ok : PointOk bodies where
  dbl hs := WP.mono (fn_ok doubleOps doubleOps_valid hs) fun _ ⟨k, e, _⟩ => ⟨k, e⟩
  add hs := WP.mono (fn_ok addAffineOps addAffineOps_valid hs) fun _ ⟨k, e, _⟩ => ⟨k, e⟩

end VG.Proof.Ed448.X86_64.Point64

namespace VG.Proof.Ed448.X86_64.Point64

open VG.Impl.Ed448.X86_64 VG.Proof.Ed448

theorem addAffineOps_keep (e : Fin 22 → Spec.X448.Fe) (i : Fin 22)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 13) ∨ i.val = 21) : evalOps addAffineOps e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ addAffineOps, (3 ≤ fopDest op ∧ fopDest op < 6) ∨ (13 ≤ fopDest op ∧ fopDest op ≤ 20) := by
      decide
    have := this op hop
    omega

end VG.Proof.Ed448.X86_64.Point64
