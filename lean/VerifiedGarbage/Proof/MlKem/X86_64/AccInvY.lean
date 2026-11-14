module

public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAccA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1

/-! ### `MlKem.X86_64.NttR.InvTop`, which only this module used -/

section

/-! ### `MlKem.X86_64.NttR.InvModel`, which only this module used -/

section

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the words of its layers

The polynomial's words after the first `st` layers of `invRules` (`LIW`):
the lazy Gentleman–Sande layers (`invW`) and the
reductions by Montgomery multiplication with `2¹⁶ mod q`. They obey the
layers `Sym.run` collapses (`modelI`), and their scaled and reduced values
(`OfI`) are the coefficients of `NTT⁻¹` (`OfI_nttInv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly invW zw PolyRep Rep inv_hop layF_rep
  nttInvLayer_eq red_rep cadd_rep mont_rep rW getElem!_map)
open VG.Proof.MlKem (wBlockN wBlk_ok layF_get nttInvBlk_ok)

/-- A layer of the words. -/
def stepI (W : WPoly) : Op → WPoly
  | .gs len => layF (wBlockN invW) W len (fun c => 256 / len - 1 - c) (128 / len)
  | .red => W.map fun w => VG.Proof.MlKem.X86_64.W.montW w rW
  | .ct _ => W

/-- The words after the first `st` layers. -/
def LIW (W : WPoly) (st : Nat) : WPoly := (invRules.ops.take st).foldl stepI W

def LfI (W : WPoly) (st p : Nat) : BitVec 16 := (LIW W st)[p]!

/-- The output word `p`: scaled by `3303` and reduced. -/
def OfI (W : WPoly) (p : Nat) : BitVec 16 := caddQ (mtW (LfI W 9 p) 512 (512 * qinvN % 65536))

theorem LIW_succ (W : WPoly) {st : Nat} {o : Op} (h : invRules.ops[st]? = some o) :
    LIW W (st + 1) = stepI (LIW W st) o := by
  unfold LIW
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem inv_ops_none {st : Nat} (h : 9 ≤ st) : invRules.ops[st]? = none :=
  List.getElem?_eq_none (by simp only [invRules, List.length_cons, List.length_nil]; omega_using [h])

/-- `vmont` with the precomputed `z q⁻¹` is `montW`, for any constant `z < q`. -/
theorem mtW_eqN (b : BitVec 16) {z : Nat} (hz : z < 3329) :
    VG.Proof.MlKem.X86_64.W.montW b (BitVec.ofNat 16 z) = mtW b z (z * qinvN % 65536) := by
  have hq : VG.Proof.MlKem.X86_64.W.qW = BitVec.ofNat 16 qN := rfl
  have hm : BitVec.ofNat 16 z * VG.Proof.MlKem.X86_64.W.qinvW = BitVec.ofNat 16 (z * qinvN % 65536) := by
    apply BitVec.eq_of_toNat_eq
    have hq' : VG.Proof.MlKem.X86_64.W.qinvW.toNat = 62209 := by decide
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hq', Nat.mod_eq_of_lt (show z < 2 ^ 16 by omega_using [hz])]
    simp only [qinvN]
    omega_using []
  rw [VG.Proof.MlKem.X86_64.W.montW, mtW, hq, lo_mul, lo_mul, lo_mul, BitVec.mul_assoc, hm]

theorem zw_zeta (k : Nat) : zw (zeta k) = BitVec.ofNat 16 (zmTab k) := by rw [zw, zmTab_eq]

theorem zmTab_lt (k : Nat) : zmTab k < 3329 := by rw [zmTab_eq]; exact Nat.mod_lt _ (by decide)

theorem invLen_pos {st len : Nat} (h : invRules.ops[st]? = some (.gs len)) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧ len ∈ [2, 4, 8, 16, 32, 64, 128] := by
  rcases Nat.lt_or_ge st 9 with hs | hs
  · rcases (by omega_using [hs] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invRules] at h <;> cases h <;> decide
  · rw [inv_ops_none hs] at h; cases h

theorem modelI (W : WPoly) (hW : ∀ p < 256, (W[p]!).toNat < 32768) : Model invRules (LfI W) (OfI W) := by
  refine ⟨fun p hp => hW p hp, fun st p p' z z' hb => ?_, fun st p p' h => ?_, fun st p p' z z' h => ?_,
    fun st p h hp => ?_, fun _ _ => rfl⟩
  · exfalso
    rcases Nat.lt_or_ge st 9 with hs | hs
    · rcases (by omega_using [hs] : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bflyOk, invRules] at hb
    · simp [bflyOk, inv_ops_none hs] at hb
  · unfold gsPairOk at h
    split at h
    · rename_i len hop
      obtain ⟨hl, hb, _⟩ := invLen_pos hop
      simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hm⟩, hp'⟩ := h
      simp only [LfI]
      rw [LIW_succ W hop, stepI, layF_get (wBlk_ok invW) _ hl _ (by rw [hb]) (by omega_using [hp']),
        ite_eq_left_of_eq_true _ _ (eq_true (show p < _ by rw [hb]; omega_using [hp'])), ite_eq_left_of_eq_true _ _ (eq_true hm)]
      rfl
    · cases h
  · unfold gsOk at h
    split at h
    · rename_i len hop
      obtain ⟨hl, hb, _⟩ := invLen_pos hop
      simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hm⟩, hp'⟩, rfl⟩, rfl⟩ := h
      have hd : (p + len) / (2 * len) = p / (2 * len) ∧ (p + len) % (2 * len) = p % (2 * len) + len ∧
          p + len - len = p := by
        have hm' := (invLen_pos hop).2.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
        rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hm]
      simp only [LfI]
      rw [LIW_succ W hop, stepI, layF_get (wBlk_ok invW) _ hl _ (by rw [hb]) hp',
        ite_eq_left_of_eq_true _ _ (eq_true (show p + len < _ by rw [hb]; omega_using [hp'])),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (p + len) % (2 * len) < len by omega_using [hd])), hd.2.2, hd.1]
      simp only [invW, zw_zeta]
      exact mtW_eqN _ (zmTab_lt _)
    · cases h
  · unfold redOk at h
    have hop : invRules.ops[st]? = some .red := by simpa using h
    simp only [LfI]
    rw [LIW_succ W hop, stepI, getElem!_map _ _ hp, ← mtW_eqN _ (zmTab_lt 0), ← zw_zeta]
    have hz : zw (zeta 0) = rW := by rw [zw, ← zmTab_eq]; decide
    rw [hz]

/-- The spec's polynomial after the first `st` layers (the reductions keep it). -/
def stepS (F : Poly) : Op → Poly
  | .gs len => nttInvLayer F len
  | .red => F
  | .ct _ => F

def GI (F : Poly) (st : Nat) : Poly := (invRules.ops.take st).foldl stepS F

theorem GI_succ (F : Poly) {st : Nat} {o : Op} (h : invRules.ops[st]? = some o) :
    GI F (st + 1) = stepS (GI F st) o := by
  unfold GI
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem rep_gs {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {st len : Nat}
    (hop : invRules.ops[st]? = some (.gs len)) {W : WPoly} {F : Poly}
    (h : PolyRep k (LIW W st) (GI F st)) : PolyRep (2 * k) (LIW W (st + 1)) (GI F (st + 1)) := by
  rw [LIW_succ W hop, GI_succ F hop, stepI, stepS, nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1) (invLen_pos hop).2.2 _ h

theorem rep_red {k st : Nat} (hop : invRules.ops[st]? = some .red) {W : WPoly} {F : Poly}
    (h : PolyRep k (LIW W st) (GI F st)) : PolyRep 1 (LIW W (st + 1)) (GI F (st + 1)) := by
  rw [LIW_succ W hop, GI_succ F hop, stepI, stepS]
  intro i hi
  rw [getElem!_map _ _ hi]
  exact red_rep (h i hi).2.2

/-- The words after the nine layers represent `NTT⁻¹`'s before the scaling, within `4 q`. -/
theorem LIW_rep (W : WPoly) (F : Poly) (h : PolyRep 1 W F) : PolyRep 4 (LIW W 9) (GI F 9) := by
  have h1 := rep_gs (k := 1) (by decide) (by decide) (st := 0) rfl h
  have h2 := rep_gs (k := 2) (by decide) (by decide) (st := 1) rfl h1
  have h3 := rep_gs (k := 4) (by decide) (by decide) (st := 2) rfl h2
  have h4 := rep_red (st := 3) rfl h3
  have h5 := rep_gs (k := 1) (by decide) (by decide) (st := 4) rfl h4
  have h6 := rep_gs (k := 2) (by decide) (by decide) (st := 5) rfl h5
  have h7 := rep_red (st := 6) rfl h6
  have h8 := rep_gs (k := 1) (by decide) (by decide) (st := 7) rfl h7
  exact rep_gs (k := 2) (by decide) (by decide) (st := 8) rfl h8

theorem GI_nine (F : Poly) : GI F 9 = nttInvLens.foldl nttInvLayer F := by
  simp only [GI, invRules, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil, stepS,
    nttInvLens]

/-- The output words are the coefficients of `NTT⁻¹`. -/
theorem OfI_nttInv (W : WPoly) (F : Poly) (h : PolyRep 1 W F) {p : Nat} (hp : p < 256) :
    (OfI W p).toNat = ((nttInv F)[p]!).val := by
  have h9 := LIW_rep W F h p hp
  have hz : zw (3303 : Zq) = BitVec.ofNat 16 512 := by decide
  have e : OfI W p = VG.Proof.MlKem.X86_64.W.caddW
      (VG.Proof.MlKem.X86_64.W.montW (LfI W 9 p) (zw (3303 : Zq))) := by
    rw [OfI, hz, mtW_eqN _ (by decide)]; rfl
  rw [e, nttInv_eq_layers, getElem!_map _ _ hp, ← GI_nine, Fin.mul_comm]
  exact cadd_rep (mont_rep 3303 h9.2.2)

end VG.Proof.MlKem.X86_64.NttR

end

end


/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers

`nttIR pb` (`pb` pass B reading the input as `src` says, as `checkI` says)
leaves `NTT⁻¹` of the input at `rdi` there, as `u32`s (`nttIR_ok`): after
`pro`, the terms of `initIB src` hold, with the polynomial's words after `st`
layers `LfI W st` for the canonical words `W` of its coefficients and their
outputs `OfI W`; pass B keeps them (`run_ok`) in the regions `rsA`, pass A
in the regions `rsB .rdi`, and `checkI` says the output's terms are `OfI W`,
which `OfI_nttInv` takes to `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR Keep)

/-- The input `F` at `p`, as `src` says: an accumulator (coefficient
`accIdx w` in word `w`). -/
def InOk : InvIn → Mem → Addr → Poly → Prop
  | .acc, m, p, F => ∀ w < 256, (wordAt m p w).toNat = (F[accIdx w]!).val

/-- The canonical words of the coefficients. -/
def canW (F : Poly) : WPoly := F.map fun x => BitVec.ofNat 16 x.val

theorem canW_get (F : Poly) {i : Nat} (hi : i < 256) : ((canW F)[i]!).toNat = (F[i]!).val := by
  rw [canW, getElem!_map _ _ hi, BitVec.toNat_ofNat]
  have := (F[i]!).isLt; simp only [q] at this; omega

theorem accIdx_lt (j : Nat) (hj : j < 256) : accIdx j < 256 := by unfold accIdx; omega_using [hj]

theorem accTerms_get {j : Nat} (hj : j < 512) :
    Y.get (accTerms.getD (j / 16) []) (j % 16) = if j < 256 then .lv 0 (accIdx j) else .junk := by
  unfold accTerms
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range (by omega_using [h]), Option.map_some, Option.getD_some, Y.get, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by decide)), Option.map_some, Option.getD_some,
      show 16 * (j / 16) + j % 16 = j by omega_using []]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega_using [h]), ← List.getD_eq_getElem?_getD]
    exact junks_get _ _ _

/-- The input's words hold the terms of `srcTerms src`. -/
theorem src_hd {src : InvIn} {m : Mem} {p : Addr} {F : Poly} (h : InOk src m p F) {O : Nat → BitVec 16}
    {j : Nat} (hj : j < 512) :
    Hd (LfI (canW F)) O (Y.get ((srcTerms src).getD (j / 16) []) (j % 16)) (wordAt m p j) := by
  cases src with
  | acc =>
    rw [srcTerms, accTerms_get hj]
    split
    · rename_i hj'
      refine Hd.of_eq (BitVec.eq_of_toNat_eq ?_)
      simp only [E.eval, LfI, LIW, List.take_zero, List.foldl_nil]
      have ha : accIdx j < 256 := accIdx_lt j hj'
      rw [canW_get _ ha, h j hj']
    · exact Hd.junk _

theorem initIB_reg (src : InvIn) (r : XReg) :
    (initIB src).reg r = if r = .xmm15 then List.replicate 16 (.c qN) else List.replicate 16 .junk := by
  cases r <;> rfl

theorem initIB_rel {src : InvIn} {F : Poly} {O : Nat → BitVec 16} {s₁ : State}
    (h : InOk src s₁.mem (s₁.gpr .rdi) F) (hq : ∀ e < 16, wd s₁ .xmm15 e = 3329) :
    Rel rsA (LfI (canW F)) O (initIB src) s₁ s₁ := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, by cases s₁; rfl,
    ⟨by simp only [initIB, rsA, List.length_cons, List.length_nil], by simp [initIB]⟩, fun _ _ => rfl⟩
  · rw [initIB_reg]
    split
    · rename_i hr; subst hr
      rw [get_replicate _ he, hq e he]; exact Hd.of_eq rfl
    · rw [get_replicate _ he]; exact Hd.junk _
  · simp only [rsA, List.length_cons, List.length_nil] at hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rw [show (initIB src).mem.getD 0 [] = junks 16 by simp only [initIB, List.getD_cons_zero], junks_get]; rfl
    · have hb : rbase rsA s₁ 1 = s₁.gpr .rdi := by simp [rbase, rsA]
      rw [show (initIB src).mem.getD 1 [] = srcTerms src by
        simp only [initIB, List.getD_cons_succ, List.getD_cons_zero], hb]
      exact src_hd h hj

/-- `nttIR pb` leaves `NTT⁻¹` of the input at `rdi` there, if `checkI src pb`. -/
theorem nttIR_ok {src : InvIn} {pb : List Instr} (hc : checkI src pb = true) {s : State} {F : Poly}
    (hS : pR (s.gpr .rsi) ∈ s.wr) (hO : pR (s.gpr .rdi) ∈ s.wr)
    (hD : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hin : InOk src s.mem (s.gpr .rdi) F) :
    WP isa (nttIR pb) s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv F) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold checkI at hc
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  unfold nttIR
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  let W := canW F
  have hM : Model invRules (LfI W) (OfI W) := modelI W fun p hp => by
    rw [canW_get _ hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (canW_get F hp)
  have hrel0 : Rel rsA (LfI W) (OfI W) (initIB src) s1 s1 :=
    initIB_rel (by rw [gdi, hm1]; exact hin) hq
  have cB : Ctx rsA s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO)
    (fun h => by cases h) (by rw [gdi, gsi]; exact hD) h8
  have cA : Ctx (rsB .rdi) s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS)
    (by rw [gdi, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO) (fun _ => by rw [gdi, k1.2.2]; exact hO)
    (by rw [gdi, gsi]; exact hD) h8
  refine WP.mono (run_ok hM cB pb hrel0 hB) fun s2 hr2 => ?_
  refine WP.mono (run_ok hM cA passIA (reframe hr2) hA) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsB .rdi) s1 1 = s.gpr .rdi := by simp [rbase, rsB, gdi]
    refine VG.Proof.MlKem.polyIs_of_toNat fun p hp => ?_
    rw [n_eq] at hp
    have h0 := hr3.mem 1 (2 * p) (by simp [rsB]) (by simp [rlen, rsB]; omega_using [hp])
    have h1 := hr3.mem 1 (2 * p + 1) (by simp [rsB]) (by simp [rlen, rsB]; omega_using [hp])
    rw [outOk_get hc (by omega_using [hp]), hb] at h0 h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [])), show 2 * p / 2 = p by omega_using []] at h0
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using []))] at h1
    have e0 := h0.eq rfl
    have e1 := h1.eq rfl
    show (coeffAt s3.mem (s.gpr .rdi) p).toNat = _
    rw [coeff_words, toNat_app16, e0, e1]
    simp only [E.eval]
    rw [OfI_nttInv W F hrep hp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsB, List.length_cons, List.length_nil] at hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega_using [hlt]
    · refine hx (pR (s.gpr .rdi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_succ, List.getD_cons_zero, gdi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rdi).toNat + 1 ≤ 1024
      omega_using [hlt]
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

end VG.Proof.MlKem.X86_64.NttR

end

end


/-!
# ML-KEM on x86-64: `NTT⁻¹` of the AVX2 accumulator

`nttInvAccY` (`Impl/MlKem/X86_64/KpkeAccY.lean`) is `NTT⁻¹` on registers
reading the accumulator (`NttR.nttIR_ok`, with `NttR.checkI_acc`).
`accIdx_add32` and `acc_word` are the accumulator's order and words, which
`FinY.lean` reads.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem accIdx_add32 {u w : Nat} (hw : w < 32) : accIdx (32 * u + w) = 32 * u + accIdx w := by
  unfold accIdx; omega

/-- Word `e` of 16 bytes loaded from `wAddr p j + 32h + 16l`. -/
theorem acc_word (m : Mem) (p : Addr) (j h l : Nat) {e : Nat} (he : e < 8) :
    word (m.readW (wAddr p j + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128) e =
      wordAt m p (j + 16 * h + 8 * l + e) := by
  rw [word_readW _ _ he, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show 32 * h + (16 * l + 2 * e) = 2 * (16 * h + 8 * l + e) by omega_using [], wAddr_add, ← wordAt]
  exact congrArg _ (by omega_using [])

theorem nttInvAccY_correct (s : State) (hs : (invAccK accY).pre s) :
    ∃ t s', Exec isa nttInvAccY s t s' ∧ abiPreserved s s' ∧ (invAccK accY).post s s' := by
  obtain ⟨F0, hF0⟩ := hs.2.2.2.2.2
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAccY s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv F0) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem :=
    WP.mono (NttR.nttIR_ok NttR.checkI_acc hw hwf hd (src := .acc) hF0) fun _ ⟨hP, hf, _⟩ => ⟨hP, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .r8] hW (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)),
    fun F hF => by rw [acc16_unique hF hF0]; exact hP⟩

end VG.Proof.MlKem.X86_64
