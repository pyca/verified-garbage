import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
import VerifiedGarbage.Spec.Ed25519.Point64

/-!
# Ed25519's point functions on x86-64: what they compute

Untrusted: everything here is checked by Lean. From `ws` in `rdi`, writable
for its 8192 bytes (`Scratch`), a function running the field program `ops`
(`fn_ok`) keeps every register but the field arithmetic's caller-saved ones
(`rax`, `rcx`, `rdx`, `r8`–`r11`): `saves` changes only `xmm0`–`xmm4`, the
program only the arithmetic's registers (`Keep`), and `restores` brings back
`rbp` and `r12`–`r15`, which `KeepReg.keeps` follows through `xmm0`–`xmm4`.
The program's values are `evalOps ops` of the slots', and it changes only the
bytes of its results (`fieldCode_frame`). The doubling's values are RFC
8032's (`dblOps_eval`), the cached addition's `pointAdd`'s (`addCachedOps_eval`).
-/

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob ofs)

variable {fld : Arith} [EdArith fld]

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

/-- `fieldCode_frame` for the whole working space. -/
theorem fieldCodeWideF_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp) :
    WP isa (.block (fieldCode fld ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Outs ops base x → t.mem x = s.mem x :=
  field_liftB hs _ (evalOps ops) (· = s.mem) (fun m => ∀ x, Outs ops base x → m x = s.mem x) rfl
    fun _ ht hp => WP.mono (fieldCode_frame ops ht) fun u ⟨k, e, f⟩ =>
      ⟨k, e, fun x hx => by rw [f x hx, hp]⟩

/-- A function running the field program `ops`: every register but the field arithmetic's
caller-saved ones kept, the slots' values `evalOps ops` of theirs, and memory changed only at
the program's results. -/
theorem fn_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true) :
    WP isa (fn fld ops) s fun t => (∀ r, (r ∉ clob ∨ r ∈ keptRegs) → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ x, Outs ops base x → t.mem x = s.mem x := by
  have hw : WP isa (fn fld ops) s fun t => (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ x, Outs ops base x → t.mem x = s.mem x := by
    simp only [fn, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (saves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_
    have hs₁ : Scratch s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    rw [WP.block_append_iff]
    refine WP.mono (fieldCodeWideF_ok hs₁ ops) fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
    refine WP.mono (restores_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ?_
    refine ⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁], by rw [m₃, e₂, m₁],
      fun x hx => by rw [m₃, f₂ x hx, m₁]⟩
    have hk' : r ∉ keptRegs := fun h => hr (by
      revert h; simp only [keptRegs, kept, clob, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
    rw [g₃ r hk', k₂.gpr r hr, g₁]
  obtain ⟨t, s', he, h⟩ := hw
  exact ⟨t, s', he, fun r hr => hr.elim (h.1 r) fun hm => Exec.gpr_keeps (hk r hm) he, h.2⟩

/-! ## The programs' values -/

/-- What `dblOps` leaves in slots 0–3. -/
def dblResult (e : Env) : Spec.Ed25519.Point :=
  let a := e 0 * e 0
  let b := e 1 * e 1
  let c := e 2 * e 2 + e 2 * e 2
  let h := a + b
  let x := (e 0 + e 1) * (e 0 + e 1)
  let ee := h - x
  let g := a - b
  let f := c + g
  ⟨ee * f, g * h, f * g, ee * h⟩

theorem dblOps_formula (e : Env) (t : Bool) :
    evalOps (dblOps t) e 0 = (dblResult e).X ∧ evalOps (dblOps t) e 1 = (dblResult e).Y ∧
      evalOps (dblOps t) e 2 = (dblResult e).Z ∧ (t = true → evalOps (dblOps t) e 3 = (dblResult e).T) := by
  cases t
  · exact ⟨rfl, rfl, rfl, nofun⟩
  · exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem dblResult_eq (e : Env) : dblResult e = Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3) := by
  simp only [dblResult, Spec.Ed25519.Point64.pointDouble, point]
  congr 1 <;> grind

/-- `dblOps` computes RFC 8032's doubling (`pointDouble`), but for `T` unless `t`. -/
theorem dblOps_eval (e : Env) (t : Bool) :
    evalOps (dblOps t) e 0 = (Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3)).X ∧
      evalOps (dblOps t) e 1 = (Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3)).Y ∧
      evalOps (dblOps t) e 2 = (Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3)).Z ∧
      (t = true → evalOps (dblOps t) e 3 = (Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3)).T) := by
  rw [← dblResult_eq]; exact dblOps_formula e t

/-- `addCachedOps` computes `pointAdd` of the point in slots 0–3 and `q`, whose cached form is
in slots 4–7, but for `T` unless `t`. -/
theorem addCachedOps_eval (e : Env) (t : Bool) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    evalOps (addCachedOps t) e 0 = (Spec.Ed25519.pointAdd (point e 0 1 2 3) q).X ∧
      evalOps (addCachedOps t) e 1 = (Spec.Ed25519.pointAdd (point e 0 1 2 3) q).Y ∧
      evalOps (addCachedOps t) e 2 = (Spec.Ed25519.pointAdd (point e 0 1 2 3) q).Z ∧
      (t = true → evalOps (addCachedOps t) e 3 = (Spec.Ed25519.pointAdd (point e 0 1 2 3) q).T) := by
  have h := pointAddCached_eval e q hq
  have e0 := congrArg Spec.Ed25519.Point.X h
  have e1 := congrArg Spec.Ed25519.Point.Y h
  have e2 := congrArg Spec.Ed25519.Point.Z h
  have e3 := congrArg Spec.Ed25519.Point.T h
  cases t
  · exact ⟨e0, e1, e2, nofun⟩
  · exact ⟨e0, e1, e2, fun _ => e3⟩

end VG.Proof.Ed25519.X86_64.Point64
