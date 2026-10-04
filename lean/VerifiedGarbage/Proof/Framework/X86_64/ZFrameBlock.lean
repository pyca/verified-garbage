import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# x86-64: what a block of vector instructions leaves of the AVX-512 registers

The VEX instructions of `VOp` (but `vzeroupper`) and the AVX-512 ones of
`ZOp` write only their destination register (`vecDst`), each of its four
lanes, and nothing but the vector registers. A block of them whose
destinations are among `rs` runs, and leaves `ZFrame rs` (`zframe_block`);
`WP.zframe` adds that to what a proof of the block says.
-/

namespace VG.X86_64

/-- The register a `VOp` writes, if it writes only one. -/
def VOp.dst? : VOp → Option XReg
  | .vbin _ _ d _ _ | .vpclmulqdq _ d _ _ _ | .vmovdqa _ d _ | .vshift _ _ d _ _ | .vpshufd _ d _ _
  | .vpalignr _ d _ _ _ | .vpblendd _ d _ _ _ | .vvar _ _ d _ _ | .vpbroadcastd _ d _ | .vpbroadcastq _ d _
  | .vpermq d _ _ | .vpermd d _ _ | .vperm2i128 d _ _ _ | .vinserti128 d _ _ _ | .vextracti128 d _ _
  | .vmovq d _ | .vsha512rnds2 d _ _ | .vsha512msg1 d _ | .vsha512msg2 d _ => some d
  | _ => none

/-- The register a `ZOp` writes. -/
def ZOp.dst : ZOp → XReg
  | .zbin _ d _ _ | .vpclmulqdq d _ _ _ | .vprold d _ _ | .vpshufd d _ _ | .vshufi32x4 d _ _ _
  | .vshift _ d _ _ | .vpslldq d _ _ | .vpsrldq d _ _ | .vpbroadcastq d _ | .vmovdqa64 d _
  | .vpternlogd d _ _ _ | .vprorq d _ _ | .vpermq d _ _ => d

/-- The register a vector instruction writes, if it writes only one and
nothing else. -/
def vecDst : Instr → Option XReg
  | .vop o => o.dst?
  | .zop o => some o.dst
  | _ => none

theorem State.zlane_setV_ne (s : State) (len : VLen) {d r : XReg} (h : r ≠ d) (lo hi : BitVec 128) (l : Nat) :
    (s.setV len d lo hi).zlane r l = s.zlane r l := by
  simp only [State.zlane, State.lane, State.setV, h, ite_false]

theorem State.zlane_setZ_ne (s : State) {d r : XReg} (h : r ≠ d) (a b c e : BitVec 128) {l : Nat} (hl : l < 4) :
    (s.setZ d a b c e).zlane r l = s.zlane r l := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]; simp [h]

theorem vecDst_ok {i : Instr} {d : XReg} (h : vecDst i = some d) (s : State) :
    ∃ s', isa.exec i s = some s' ∧ VKeep s s' ∧ ∀ r, r ≠ d → ∀ l < 4, s'.zlane r l = s.zlane r l := by
  cases i
  all_goals try (simp only [vecDst, reduceCtorEq] at h)
  · rename_i o
    cases o <;> simp only [VOp.dst?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      refine ⟨_, rfl, ?_, fun r hr l _ => ?_⟩
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | (simp only [VOp.exec]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | (simp only [VOp.exec]; exact State.zlane_setV_ne _ _ hr _ _ _)
      | (simp only [VOp.exec]; split <;> exact State.zlane_setV_ne _ _ hr _ _ _)
  · rename_i o
    simp only [Option.some.injEq] at h; subst h
    refine ⟨_, rfl, ?_, fun r hr l hl => ?_⟩
    · cases o <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases o <;> exact State.zlane_setZ_ne _ hr _ _ _ _ hl

/-- A block of vector instructions writing only registers among `rs` runs and
leaves `ZFrame rs`. -/
theorem zframe_block (rs : List XReg) : ∀ (is : List Instr),
    is.all (fun i => (vecDst i).any (· ∈ rs)) = true → ∀ s,
    ∃ s', runBlock isa is s = some s' ∧ ZFrame rs s s'
  | [], _, s => ⟨s, rfl, ZFrame.refl _ _⟩
  | i :: is, h, s => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨d, hd, hdr⟩ : ∃ d, vecDst i = some d ∧ d ∈ rs := by
      have h1 := h.1
      cases e : vecDst i with
      | none => rw [e] at h1; exact absurd h1 (by simp)
      | some d => rw [e] at h1; exact ⟨d, rfl, by simpa using h1⟩
    obtain ⟨s₁, e₁, k₁, z₁⟩ := vecDst_ok hd s
    obtain ⟨s', e', f'⟩ := zframe_block rs is h.2 s₁
    refine ⟨s', by show (isa.exec i s).bind _ = _; rw [e₁, Option.bind_some]; exact e', ?_⟩
    exact (ZFrame.trans ⟨k₁.gpr, k₁.mem, k₁.rd, k₁.wr, fun r hr l hl =>
      z₁ r (fun e => hr (e ▸ hdr)) l hl⟩ f')

/-- What a proof of a block of vector instructions says, and `ZFrame`. -/
theorem WP.zframe {is : List Instr} {rs : List XReg} (hd : is.all (fun i => (vecDst i).any (· ∈ rs)) = true)
    {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q) :
    WP isa (.block is) s fun s' => Q s' ∧ ZFrame rs s s' := by
  obtain ⟨s', e, q⟩ := WP.runBlock_of h
  obtain ⟨s'', e', f⟩ := zframe_block rs is hd s
  rw [e, Option.some.injEq] at e'
  subst e'
  exact WP.of_runBlock ⟨s', e, q, f⟩

end VG.X86_64
