import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsMixed
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Mont.Read

/-!
# Point operations as functions on x86-64: from the contracts to the bodies

A function `wrap body` of `Impl/Weierstrass/X86_64/PointOps.lean`, from a
state with `ws` in `rdi`, writable for its 8192 bytes, apart from the return
address (`fnPre`), the curve's `p` at its slot and the coordinates it reads
below `p`: the field invariant holds of the slots it reads, with their
values (`env`), so a run of `body` that leaves `R` holding `r` of them,
writing only `W`, makes the function's run (`fn_ok`): the calling
convention kept (the callee-saved registers `restores` brings back, the
others untouched, the return address apart from `ws`), `R`'s coordinates
below `p` and standing for `r`, and every byte of `ws` kept but those of
`W` and the products' temporary area, which the curve's facts (`FnCfg`)
place in the function's own working space or `P`.
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Weierstrass.X86_64.PointOps

/-- `ws` in `rdi`, writable for its 8192 bytes, apart from the return address,
not wrapping around. -/
def fnPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 8192⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩ ∧
    (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64

/-- The values the slots of `ws` stand for, as the proofs decode them. -/
def env (m n : Nat) [NeZero m] (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * n)) (wordsVal mem base x n)

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (C : Spec.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.coordAt m ws o = wordsVal m ws o C.k := by
  unfold Spec.Weierstrass.Point.Curve.coordAt Spec.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws C.k o

/-- What the proofs need of a curve's functions, with the code's slots
`K`: `R`, `E` (`P`, `Q`) and the modulus where the specification has them,
the slots `Sl` laid out for the field arithmetic, which finds its modulus
at its slot, and the slots the bodies write (`W`) and the temporary area
in the own working space or `P`. -/
structure FnCfg (K : WinCfg) (C : VG.Spec.Weierstrass.PointOps.Curve) (Sl : Nat → Prop) : Prop where
  n : K.M.n = C.k
  rx : K.R.x = C.pAt
  ry : K.R.y = C.pAt + 8 * C.k
  rz : K.R.z = C.pAt + 16 * C.k
  ex : K.E.x = C.qAt
  ey : K.E.y = C.qAt + 8 * C.k
  ez : K.E.z = C.qAt + 16 * C.k
  mo : K.M.mo = C.modAt
  lay : Lay K.M 8192 Sl
  modOk : ∀ (mem : Mem) (base : Addr), wordsVal mem base K.M.mo K.M.n = C.p → ModOkW K.M 8192 C.p mem base
  keep : ∀ i < 8192, ¬ C.Own i → (i < C.pAt ∨ C.pAt + C.ptBytes ≤ i) →
    (∀ w ∈ rcbW K.S K.D ++ jacCoords K.R, i < w ∨ w + 8 * K.M.n ≤ i) ∧
    (i < K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ i)
  small : C.pAt + C.ptBytes ≤ 8192
  wsl : ∀ w ∈ rcbW K.S K.D ++ jacCoords K.R, Sl w
  clob : ∀ r ∈ keptRegs, r ∈ clob K.M.n
  odd : C.p % 2 = 1

/-- The field arithmetic writes no register outside these. -/
theorem mem_clob_sub {n : Nat} {r : Reg} (h : r ∈ clob n) :
    r ∈ [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have := List.mem_of_mem_take h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · split at h <;> simp at h <;> rcases h with rfl | rfl <;> decide

/-- The field invariant of the slots `V` a function reads, from its precondition. -/
theorem inv_of {K : WinCfg} {C : VG.Spec.Weierstrass.PointOps.Curve} {Sl : Nat → Prop} (hF : FnCfg K C Sl)
    {V : List Nat} (hV : ∀ x ∈ V, Sl x) {s : State} (hs : fnPre s) (hmod : C.ModOk (s.gpr .rdi) s.mem)
    (hlt : ∀ x ∈ V, wordsVal s.mem (s.gpr .rdi) x K.M.n < C.p) :
    Inv K.M (s.gpr .rdi) 8192 C.p Sl V (env C.p K.M.n s.mem (s.gpr .rdi)) s := by
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  have hbig : C.modAt < 2 ^ 32 := by have := hF.small; simp only [VG.Spec.Weierstrass.PointOps.Curve.modAt, VG.Spec.Weierstrass.PointOps.Curve.slot, VG.Spec.Weierstrass.PointOps.Curve.ptBytes, VG.Spec.Weierstrass.PointOps.Curve.pAt] at *; omega
  have hmv : wordsVal s.mem (s.gpr .rdi) K.M.mo K.M.n = C.p := by
    rw [hF.mo, hF.n, ← coordAt_eq C.toCurve s.mem _ hbig]; exact hmod
  exact ⟨⟨rfl, by rw [hwr]; simp, hnw⟩, hF.modOk _ _ hmv, hV, hlt, fun _ _ => rfl⟩

/-- `Inv` for other values of the slots `V` that agree on them. -/
theorem _root_.VG.Proof.Weierstrass.X86_64.Inv.congr_env {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E E' : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) (he : ∀ x ∈ V, E x = E' x) :
    Inv M base size m Sl V E' s :=
  ⟨h.scr, h.mod, h.sl, h.lt, fun x hx => (h.val x hx).trans (he x hx)⟩

/-- A function `wrap body` whose body leaves `R` holding `r` of the values
of the slots `V`, writing only `rcbW K.S K.D` and `R`: its run. -/
theorem fn_ok {K : WinCfg} {C : VG.Spec.Weierstrass.PointOps.Curve} {Sl : Nat → Prop} (hF : FnCfg K C Sl) {body : Prog isa}
    {V : List Nat} {r : (Nat → Fin C.p) → Fin C.p × Fin C.p × Fin C.p}
    (hok : wrapOk (wrap body) = true) (hnc : body.noCalls = true)
    (hV : ∀ x ∈ V, Sl x)
    (hb : ∀ (s : State) (E : Nat → Fin C.p), Inv K.M (s.gpr .rdi) 8192 C.p Sl V E s →
      WP isa body.inline s fun t => ProgKeep K.M (s.gpr .rdi) (rcbW K.S K.D ++ jacCoords K.R) s t ∧
        ∃ E', Inv K.M (s.gpr .rdi) 8192 C.p Sl (jacCoords K.R) E' t ∧ (E' K.R.x, E' K.R.y, E' K.R.z) = r E)
    (s : State) (hs : fnPre s) (hmod : C.ModOk (s.gpr .rdi) s.mem)
    (hlt : ∀ x ∈ V, wordsVal s.mem (s.gpr .rdi) x K.M.n < C.p) :
    ∃ t s', Exec isa (wrap body) s t s' ∧ abiPreserved s s' ∧
      C.Below (C.pointAt s'.mem (s.gpr .rdi) C.pAt) ∧
      (env C.p C.k s'.mem (s.gpr .rdi) C.pAt, env C.p C.k s'.mem (s.gpr .rdi) (C.pAt + 8 * C.k),
        env C.p C.k s'.mem (s.gpr .rdi) (C.pAt + 16 * C.k)) = r (env C.p K.M.n s.mem (s.gpr .rdi)) ∧
      C.Keeps C.pAt (s.gpr .rdi) s.mem s'.mem := by
  obtain ⟨hvec, hmx⟩ := wrapOk_spec hok
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  have hbig : C.modAt < 2 ^ 32 := by have := hF.small; simp only [VG.Spec.Weierstrass.PointOps.Curve.modAt, VG.Spec.Weierstrass.PointOps.Curve.slot, VG.Spec.Weierstrass.PointOps.Curve.ptBytes, VG.Spec.Weierstrass.PointOps.Curve.pAt] at *; omega
  have hmv : wordsVal s.mem (s.gpr .rdi) K.M.mo K.M.n = C.p := by
    rw [hF.mo, hF.n, ← coordAt_eq C.toCurve s.mem _ hbig]; exact hmod
  have hI : Inv K.M (s.gpr .rdi) 8192 C.p Sl V (env C.p K.M.n s.mem (s.gpr .rdi)) s :=
    ⟨⟨rfl, by rw [hwr]; simp, hnw⟩, hF.modOk _ _ hmv, hV, hlt, fun _ _ => rfl⟩
  have hw : WP isa (wrap body) s fun u => ProgKeep K.M (s.gpr .rdi) (rcbW K.S K.D ++ jacCoords K.R) s u ∧
      ∃ E', Inv K.M (s.gpr .rdi) 8192 C.p Sl (jacCoords K.R) E' u ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) = r (env C.p K.M.n s.mem (s.gpr .rdi)) := by
    refine wrap_keep_ok hF.clob (P := fun x => x.gpr .rdi = s.gpr .rdi ∧
        Inv K.M (s.gpr .rdi) 8192 C.p Sl V (env C.p K.M.n s.mem (s.gpr .rdi)) x)
      (F := fun u => ∃ E', Inv K.M (s.gpr .rdi) 8192 C.p Sl (jacCoords K.R) E' u ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) = r (env C.p K.M.n s.mem (s.gpr .rdi)))
      (fun x y _ k _ hx => ⟨(k.1 .rdi (by simp)).trans hx.1, hx.2.of_keeps k (by simp)⟩)
      (fun x y _ k _ ⟨E', hi, he⟩ => ⟨E', hi.of_keeps k (by decide), he⟩) ⟨rfl, hI⟩ fun x ⟨hx, ix⟩ => ?_
    rw [← Code.inline_of_noCalls hnc]
    have := hb x _ (hx ▸ ix)
    rw [hx] at this
    exact this
  obtain ⟨t, s', he, hk', E', hi', hv'⟩ := hw
  have hret' : ∀ x, (x - s.gpr .rsp).toNat < 8 → 8192 ≤ (x - s.gpr .rdi).toNat := by
    intro x hx
    have := hret x (by simp only [Region.Contains]; omega)
    simp only [Region.Contains] at this
    omega
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun x hx => ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases hm : x ∈ keptRegs
    · exact wrap_gpr hvec hnc he x hm
    · exact hk'.gpr x fun hc => by
        have := mem_clob_sub hc
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
        simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hm
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this hm
  · refine Mem.readW_congr fun i hi => hk'.mem _ (fun w hw => Or.inr ?_) (Or.inr ?_)
    · have := hret' (s.gpr .rsp + BitVec.ofNat 64 i) (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      have := hF.lay.le w (hF.wsl w hw)
      simp only [ofs]; omega
    · have := hret' (s.gpr .rsp + BitVec.ofNat 64 i) (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      have := (hF.modOk _ _ hmv).tmp
      simp only [ofs]; omega
  · have hs := hF.small
    simp only [VG.Spec.Weierstrass.PointOps.Curve.ptBytes] at hs
    have l := fun x hx => hi'.lt x hx
    rw [hF.n] at l
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Spec.Weierstrass.Point.Curve.pointAt, Spec.Weierstrass.Point.elemBytes] <;>
      rw [coordAt_eq _ _ _ (by omega)]
    · rw [← hF.rx]; exact l _ (by simp [jacCoords])
    · rw [← hF.ry]; exact l _ (by simp [jacCoords])
    · rw [show 2 * (8 * C.k) = 16 * C.k by omega, ← hF.rz]; exact l _ (by simp [jacCoords])
  · rw [← hv']
    have v := fun x hx => hi'.val x hx
    rw [hF.n] at v
    simp only [env]
    rw [← hF.rz, ← hF.ry, ← hF.rx, v _ (by simp [jacCoords]), v _ (by simp [jacCoords]),
      v _ (by simp [jacCoords])]
  · intro i hi hown hp
    have k := hF.keep i hi hown hp
    have e : ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i :=
      Mem.sub_ofNat_toNat _ (by simp only [Spec.Weierstrass.Mont.wsBytes] at hi; omega)
    exact hk'.mem _ (fun w hw => by rw [e]; exact k.1 w hw) (by rw [e]; exact k.2)

/-- Equal bytes give equal numbers: the `k` words at `x` when the `n` bytes
from `o` agree, for `[x, x + 8 k)` within them. -/
theorem wordsVal_of_bytes {ws : Addr} {m₁ m₂ : Mem}
    {o n : Nat} (h : VG.Spec.Weierstrass.PointOps.Curve.bytes ws m₁ o n =
      VG.Spec.Weierstrass.PointOps.Curve.bytes ws m₂ o n) {x k : Nat} (hx : o ≤ x)
    (hk : x + 8 * k ≤ o + n) : wordsVal m₁ ws x k = wordsVal m₂ ws x k := by
  rw [← read_eq_wordsVal, ← read_eq_wordsVal]
  congr 1
  refine Mem.read_congr fun i hi => ?_
  have hj : x - o + i < n := by omega
  have e := congrArg (fun l => l[x - o + i]?) h
  simp only [Spec.Weierstrass.PointOps.Curve.bytes, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.some.injEq] at e
  have ha : ws + BitVec.ofNat 64 (o + (x - o + i)) = off ws x + BitVec.ofNat 64 i := by
    rw [off, BitVec.add_assoc, ← BitVec.ofNat_add, show o + (x - o + i) = x + i by omega]
  rw [← ha]
  exact BitVec.toNat_inj.mp e

/-- The bytes of `a ++ b` determine those of `a` and `b`, for `a`'s of the
same length. -/
theorem append_bytes {a b c d : List Nat} (h : a ++ b = c ++ d) (hl : a.length = c.length) :
    a = c ∧ b = d := List.append_inj h hl

end VG.Proof.Weierstrass.X86_64.PointOps
