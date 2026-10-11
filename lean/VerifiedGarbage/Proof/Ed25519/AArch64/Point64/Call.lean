import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Ed25519 on AArch64: calls of the point functions

Untrusted: everything here is checked by Lean. A call (`Point64.call`, with
the return address kept in `v31`) of a function running a field program
`ops` (`fn ops`), from the field code's state (`Scr`), is the program inlined:
it keeps what a field operation keeps (`Keep`), leaves the slots' values
`evalOps ops` of theirs, and writes only the program's results' slots
(`call_ok`). The call runs on the working space alone (`WP.callV`, with the
function's own proof, `fn_ok`, as its contract, `callK`).
-/

namespace VG.Proof.Ed25519.AArch64.Point64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Point64 VG.Proof.Ed25519.AArch64

/-- The contract of a call of `fn ops`, from `fn_ok`. -/
def callK (ops : List FieldOp) (base : Addr) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .x0 = base ∧ base.toNat + 8192 ≤ 2 ^ 64
  post t t' := (∀ r, r ∉ clob → t'.gpr r = t.gpr r) ∧
    (∀ x, Unwritten ops base x → t'.mem x = t.mem x) ∧
    env t'.mem base = evalOps ops (env t.mem base) ∧ t'.v .v31 = t.v .v31
  pub _ _ := True

/-- Every slot is in bytes 64 to 767. -/
theorem unwritten_of (ops : List FieldOp) {base x : Addr} (hx : ofs base x < 64 ∨ 64 + 704 ≤ ofs base x) :
    Unwritten ops base x := fun op _ => by
  have := (fieldDest op).isLt
  simp only [offset]
  omega

/-- **A call** of the function running `ops`, as `ops` inlined. -/
theorem call_ok {name : String} {ops : List FieldOp}
    (hv : ∀ r, ∀ i ∈ fieldCode ops, vdstOf i ≠ some r) (hkv : (fn ops).allInstrs keepsV = true)
    (hnf : (fn ops).noFrames = true) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (Point64.call name (fn ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Unwritten ops base x → t.mem x = s.mem x := by
  have hv31 : ∀ i ∈ instrs (fn ops), vdstOf i ≠ some .v31 := fun i hi => by
    unfold fn at hi
    simp only [instrs, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨k, hk, rfl⟩ | hi | ⟨k, hk, rfl⟩
    · revert k; decide
    · exact hv _ i hi
    · intro h; nomatch h
  unfold Point64.call
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v31, 0)] s (by decide) (by decide))
    fun s₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, _⟩ => ?_
  rw [WP.seq_iff]
  have hcov : Covers [⟨base, 8192⟩] s₁.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, w₁]; exact hs.wr
  have hx0 : s₁.gpr .x0 = base := by rw [g₁]; exact hs.x0
  refine WP.callV (k := callK ops base) (rd := []) (wr := [⟨base, 8192⟩]) ?hv
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hx0], hs.nowrap⟩
    (Covers.right hcov) hcov ?_ hnf
  case hv =>
    intro t ⟨_, hwr, h0, hn⟩
    obtain ⟨tr, t', he, hg, hrd, hwr', hsp, hmem, hev⟩ :=
      fn_ok (s := t) (base := base) ⟨h0, by rw [hwr]; exact List.mem_singleton_self _, hn⟩ ops hv
    exact ⟨tr, t', he, ⟨fun r hr => hg r (fn_preserved r hr), hsp, Exec.preservedV he hkv⟩,
      fun r hr => hg r (.inl hr), hmem, hev, Exec.vec hv31 he⟩
  intro t hrd hwr hsp _ _ _ _ ⟨hg, hmem, hev, hv31'⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, m₁] at hg hmem hev
  refine WP.mono (umovOf_ok [(.x30, .v31, 0)] t (by decide) (by decide))
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  have l30 : u.gpr .x30 = s.gpr .x30 := by
    rw [uls _ List.mem_cons_self, ← l₁ _ List.mem_cons_self]
    exact congrArg (BitVec.extractLsb' (64 * 0) 64) hv31'
  refine ⟨⟨fun r hr => ?_, by rw [ur, hrd, r₁], by rw [uw, hwr, w₁], by rw [usp, hsp, sp₁],
    fun x hx => by rw [um]; exact hmem x (unwritten_of ops hx)⟩, by rw [um, hev],
    fun x hx => by rw [um]; exact hmem x hx⟩
  by_cases h30 : r = .x30
  · rw [h30]; exact l30
  · have hl : r ∉ linkRegs := by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by rw [h]; decide), fun h => hr (by rw [h]; decide), h30⟩
    rw [uoth r (by simpa using h30), hg r hr, State.callEntry_gpr _ hl, g₁]

theorem doubleFn_noFrames : doubleFn.noFrames = true := by decide +kernel

theorem affFn_noFrames : affFn.noFrames = true := by decide +kernel

/-- **A call of `vg_ed25519_r64_double_ext`**, as RFC 8032's doubling inlined. -/
theorem doubleCall_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa doubleCall s fun t => Keep base s t ∧
      env t.mem base = evalOps doubleRfcOps (env s.mem base) ∧
      ∀ x, Unwritten doubleRfcOps base x → t.mem x = s.mem x :=
  call_ok doubleRfcOps_vdst doubleFn_keepsV doubleFn_noFrames hs

/-- **A call of `vg_ed25519_r64_add_affine_ext`**, as the affine addition inlined. -/
theorem affCall_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa affCall s fun t => Keep base s t ∧
      env t.mem base = evalOps addAffineOps (env s.mem base) ∧
      ∀ x, Unwritten addAffineOps base x → t.mem x = s.mem x :=
  call_ok addAffineOps_vdst affFn_keepsV affFn_noFrames hs

end VG.Proof.Ed25519.AArch64.Point64
