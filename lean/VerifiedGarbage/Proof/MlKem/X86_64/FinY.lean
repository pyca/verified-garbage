module

public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
meta import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
meta import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeAcc
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAccA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1

/-! ### `MlKem.X86_64.AccInvY`, which this module and modules that import it used -/

section

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

end

end

/-! ### `MlKem.X86_64.YAddSub`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: addition and subtraction with AVX2, which the K-PKE functions inline

Each iteration of the loop loads eight coefficients of `f` and of `g` and, in
each lane, does what an iteration of `vg_mlkem_add` (`vg_mlkem_sub`) does
(`AddSub.lean`): the same arithmetic (`addArith_ok`, `subArith_ok`), whose
proof holds of each lane (`ylanes`); it stores the eight results to `f`
(`YAddSub.step`), and the loop leaves `f` with all 256 (`YAddSub.fn_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The arithmetic of a lane -/

theorem addArith_ok (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block addArith) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = cadd32 (dword (s.xmm .xmm0) j + dword (s.xmm .xmm1) j - 3329#32)) ∧
        XOnly [.xmm0, .xmm1] s s' := by
  simp only [addArith, dcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  refine ⟨fun j hj => ?_, by xonly⟩
  simp only [dword_paddd _ _ hj, dword_psubd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
  rfl

theorem subArith_ok (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block subArith) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = cadd32 (dword (s.xmm .xmm0) j - dword (s.xmm .xmm1) j)) ∧
        XOnly [.xmm0, .xmm1] s s' := by
  simp only [subArith, dcadd, xmov, xb]
  vrun [eval_movdqa]
  refine ⟨fun j hj => ?_, by xonly⟩
  simp only [dword_psubd _ _ hj, dword_paddd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
  rfl

theorem lane_addArith : laneSseBlock (toY addArith) = some addArith := by decide +kernel

theorem lane_subArith : laneSseBlock (toY subArith) = some subArith := by decide +kernel

/-! ## The loop -/

namespace YAddSub

/-- After `i` vectors of eight, each coefficient before `8i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i)
  rsi : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qD
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

theorem in32 {rs : List Region} {p : Addr} (hw : pR p ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (coeffAddr p j) 32 :=
  ⟨_, hw, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

/-- Doubleword `e` of lane `l` of a 256-bit load of coefficient `j`. -/
theorem lane_coeff (m : Mem) (p : Addr) (j l e : Nat) (he : e < 4) :
    dword (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * l)) 128) e = coeffAt m p (j + 4 * l + e) := by
  rw [dword_readW _ _ he, show 16 * l = 4 * (4 * l) by omega_using [], coeffAddr_off p j (4 * l),
    coeffAddr_off p (j + 4 * l) e, ← coeffAt_eq]

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀) {ar : List Instr}
  {L : BitVec 32 → BitVec 32 → BitVec 32}
  (hF : ∀ (s : State), s.xmm .xmm15 = qD →
    WP isa (.block ar) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = L (dword (s.xmm .xmm0) j) (dword (s.xmm .xmm1) j)) ∧
        XOnly [.xmm0, .xmm1] s s')
  (hY : laneSseBlock (toY ar) = some ar)
include hp hF hY

/-- An iteration, which stores `L` of the coefficients of `f` and `g`. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (yaccBody ar ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega_using [hi]
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]
  have e2 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]
  rw [yaccBody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact in32 (List.mem_append_right _ hw) j0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact in32 hr j0)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY (P := fun l t => ∀ j < 4, dword (t.xmm .xmm0) j =
      L (dword ((s2.proj l).xmm .xmm0) j) (dword ((s2.proj l).xmm .xmm1) j))
    fun l hl => hF _ (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have g3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .rdi) 32 := by rw [o13.wr, g3]; exact in32 hw j0
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi, show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi, show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega_using [h])]
      obtain ⟨l, e, hl, he, hk'⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 8 * i + 4 * l + e :=
        ⟨(k - 8 * i) / 4, (k - 8 * i) % 4, by omega_using [h], by omega_using [], by omega_using [h]⟩
      subst hk'
      rw [show 8 * (4 * (8 * i + 4 * l + e - 8 * i)) = 8 * (16 * l + 4 * e) by omega_using [], extract_ymm _ _ hl he,
        ← State.proj_xmm, B3 l hl e he, State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl, L1 l hl,
        L2 l hl, o1.gpr, o1.mem, e1, e2, lane_coeff _ _ _ _ _ he, lane_coeff _ _ _ _ _ he,
        hI.coeff _ (by omega_using [hi, hl, he]), ifn (by omega_using []),
        coeffAt_congr (bytes_frame hI.frame (by simpa using hp.2.2.1.symm) (by decide)) (by rw [n_eq]; omega_using [hi, hl, he])]
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega_using [h'])]
      · rw [ifn h', ifn (by omega_using [h, h'])]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

/-- The whole function, from its precondition. -/
theorem fn_ok (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (accAvx2 ar) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (accAvx2 ar : Prog isa) = true) :
    ∃ tr s', Exec isa (accAvx2 ar) s₀ tr s' ∧ abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hW : WP isa (accAvx2 ar) s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k =
        L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    refine WP.seq (WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy], lq l hl]; decide,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega_using [])]⟩)
      fun i hi u hI => step hp hF hY hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega_using [hk])]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hco k hk]
    exact hv k hk

end

end YAddSub

/-! ## The functions -/

theorem addY_correct (s : State) (hs : (accK Spec.MlKem.add).pre s) :
    ∃ t s', Exec isa addAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.add).post s s' :=
  YAddSub.fn_ok hs (L := fun a b => cadd32 (a + b - 3329#32)) addArith_ok lane_addArith
    (fun i hi => by
      rw [add_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        add_get _ _ (by rw [n_eq]; exact hi), val_add,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide +kernel) (by decide +kernel)

theorem subY_correct (s : State) (hs : (accK Spec.MlKem.sub).pre s) :
    ∃ t s', Exec isa subAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.sub).post s s' :=
  YAddSub.fn_ok hs (L := fun a b => cadd32 (a - b)) subArith_ok lane_subArith
    (fun i hi => by
      rw [sub_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        sub_get _ _ (by rw [n_eq]; exact hi), val_sub,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide +kernel) (by decide +kernel)

theorem addY_ct : ConstantTime isa (accK Spec.MlKem.add).pre (accK Spec.MlKem.add).pub addAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem subY_ct : ConstantTime isa (accK Spec.MlKem.sub).pre (accK Spec.MlKem.sub).pub subAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the AVX2 accumulator added to a polynomial

`finAccY` (`Impl/MlKem/X86_64/KpkeAccY.lean`) adds the accumulator in words
at `rsi` to the `u32`s at `rdi`, 32 coefficients an iteration. Of the two
registers of words it loads, `vpunpcklwd` and `vpunpckhwd` (`L` and `H`)
put coefficient `8q + 4l + e` of the 32 (`q < 4`, `e < 4`) at word
`4(q mod 2) + e` of lane `l` of `L` (`q < 2`) or `H`: the accumulator's word
`srcF q l e` (`srcF_ok`). `vpunpcklwd` or `vpunpckhwd` with zero extends
those four words to doublewords (`dword_unpk0`), and `vg_mlkem_add_avx2`'s
arithmetic adds them to the eight `u32`s at `rdi + 32q` (`finQ_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

namespace FinY

/-- The word of an iteration's 32 (of the accumulator) whose coefficient is
`8q + 4l + e`. -/
def srcF (q l e : Nat) : Nat := 16 * (e % 2) + 8 * l + 2 * q + e / 2

theorem srcF_ok : ∀ q < 4, ∀ l < 2, ∀ e < 4, srcF q l e < 32 ∧ accIdx (srcF q l e) = 8 * q + 4 * l + e := by
  decide +kernel

theorem word_zero128 {i : Nat} : word (0 : BitVec 128) i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [getLsbD_word]

/-- Doubleword `e` of `vpunpcklwd` (`h = 0`) or `vpunpckhwd` (`h = 1`) of `a`
and zero: word `4h + e` of `a`. -/
theorem dword_unpk0 (a : BitVec 128) {h : Nat} (hh : h < 2) {e : Nat} (he : e < 4) :
    (dword (XBinOp.eval (if h = 0 then .punpcklwd else .punpckhwd) a 0) e).toNat = (word a (4 * h + e)).toNat := by
  rw [dword_eq_words _ he]
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
  · simp (disch := omega_arith) only [word_punpcklwd, Nat.mul_mod_right, Nat.add_mod, Nat.mul_zero, Nat.zero_add,
      Nat.one_mod, ↓reduceIte]
    simp only [Nat.one_ne_zero, ite_false, word_zero128, show 2 * e / 2 = e by omega_arith,
      show BitVec.toNat (0 : BitVec 16) = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · simp (disch := omega_arith) only [Nat.one_ne_zero, word_punpckhwd, Nat.mul_mod_right, Nat.add_mod, Nat.zero_add,
      Nat.one_mod, ↓reduceIte]
    simp only [word_zero128, show 4 + 2 * e / 2 = 4 * 1 + e by omega_arith,
      show BitVec.toNat (0 : BitVec 16) = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- In a lane: a word of `w` unpacked with `xmm14` (`op`), added to `xmm0` with
`vg_mlkem_add`'s arithmetic. -/
theorem unpkAdd_ok (w : XReg) (op : XBinOp) (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block ([xb .movdqa .xmm1 w, xb op .xmm1 .xmm14] ++ addArith)) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j =
        cadd32 (dword (s.xmm .xmm0) j + dword (XBinOp.eval op (s.xmm w) (s.xmm .xmm14)) j - 3329#32)) ∧
      XOnly [.xmm1, .xmm0, .xmm1] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.xmm .xmm1 = XBinOp.eval op (s.xmm w) (s.xmm .xmm14) ∧ XOnly [.xmm1] s s1)
    (by
      simp only [xb]
      vrun [eval_movdqa]
      exact ⟨trivial, by xonly⟩) fun s1 ⟨h1, o1⟩ => ?_
  refine WP.mono (addArith_ok s1 (by rw [o1.xmm _ (by decide), hq])) fun s2 ⟨h2, o2⟩ =>
    ⟨fun j hj => ?_, o1.trans o2⟩
  rw [h2 j hj, h1, o1.xmm _ (by decide)]

/-- `finQ w op off`: the eight `u32`s at `rdi + off` plus the words of `w`
unpacked with `xmm14` (`op`), by `vg_mlkem_add_avx2`'s arithmetic, stored back. -/
theorem finQ_ok {w : XReg} (hw0 : w ≠ .xmm0) {op : VBinOp} {xop : XBinOp}
    (hl : laneSseBlock ([yb op .xmm1 w .xmm14] ++ toY addArith) =
      some ([xb .movdqa .xmm1 w, xb xop .xmm1 .xmm14] ++ addArith))
    {off : Nat} {s : State} (hq : ∀ l < 2, s.lane .xmm15 l = qD)
    (hin : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 off) 32) :
    WP isa (.block (finQ w op off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 off) (s'.ymm .xmm0) ∧
      (∀ l < 2, ∀ e < 4, dword (s'.lane .xmm0 l) e =
        cadd32 (dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e +
          dword (XBinOp.eval xop (s.lane w l) (s.lane .xmm14 l)) e - 3329#32)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧
      ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, s'.lane r l = s.lane r l := by
  obtain hin' : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 off) 32 :=
    let ⟨r, hr, hc⟩ := hin; ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show finQ w op off = [.vmovdquLoad .l256 .xmm0 (at_ .rdi off)] ++
      (([yb op .xmm1 w .xmm14] ++ toY addArith) ++ [.vmovdquStore .l256 (at_ .rdi off) .xmm0]) from rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok hin') fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hl (P := fun l t => ∀ j < 4, dword (t.xmm .xmm0) j =
      cadd32 (dword ((s1.proj l).xmm .xmm0) j +
        dword (XBinOp.eval xop ((s1.proj l).xmm w) ((s1.proj l).xmm .xmm14)) j - 3329#32))
    fun l hl' => unpkAdd_ok w xop _ (by rw [State.proj_xmm, o1.lane _ (by decide) l hl']; exact hq l hl'))
    fun s2 ⟨L2, o2⟩ => ?_
  obtain o12 := o1.trans o2
  refine WP.mono (yst_ok (h := .xmm0) (by rw [o12.wr, o12.gpr]; exact hin)) fun s3 e3 => ?_
  subst e3
  refine ⟨by simp only [State.setMem_mem, State.setMem_ymm]; rw [o12.mem, o12.gpr], fun l hl' e he => ?_,
    by simp only [State.setMem_gpr]; exact o12.gpr, by simp only [State.setMem_rd]; exact o12.rd,
    by simp only [State.setMem_wr]; exact o12.wr, ?_, fun r hr l hl' => ?_⟩
  · simp only [State.setMem_lane]
    rw [← State.proj_xmm, L2 l hl' e he, State.proj_xmm, State.proj_xmm, State.proj_xmm, L1 l hl',
      o1.lane _ (by simpa using hw0) l hl', o1.lane _ (by decide) l hl']
  · rw [show (s2.setMem _).mxcsr = s2.mxcsr by cases s2; rfl]; exact o12.mxcsr
  · simp only [State.setMem_lane]; exact o12.lane r (by simpa [or_comm, or_left_comm] using hr) l hl'

/-- The first `8j` coefficients at `tP` are those of `E + F`, and the others
those of `m₀`. -/
def MemOk (m₀ : Mem) (tP : Addr) (E F : Poly) (j : Nat) (m : Mem) : Prop :=
  ∀ c < 256, (c < 8 * j → (coeffAt m tP c).toNat = ((add E F)[c]!).val) ∧
    (8 * j ≤ c → coeffAt m tP c = coeffAt m₀ tP c)

/-- `finQ` on the coefficients `8j, …, 8j + 7`. -/
theorem finQ_step {tP : Addr} {m₀ : Mem} {E F : Poly}
    (hE : ∀ c < 256, (coeffAt m₀ tP c).toNat < q ∧ (E[c]!).val = (coeffAt m₀ tP c).toNat)
    {w : XReg} (hw0 : w ≠ .xmm0) {op : VBinOp} {xop : XBinOp}
    (hl : laneSseBlock ([yb op .xmm1 w .xmm14] ++ toY addArith) =
      some ([xb .movdqa .xmm1 w, xb xop .xmm1 .xmm14] ++ addArith)) {h : Nat}
    (hop : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval xop a 0) e).toNat = (word a (4 * h + e)).toNat)
    {j off : Nat} (hj : j < 32) {u : State}
    (hrdi : u.gpr .rdi + BitVec.ofNat 64 off = coeffAddr tP (8 * j))
    (hq : ∀ l < 2, u.lane .xmm15 l = qD) (hz : ∀ l < 2, u.lane .xmm14 l = 0)
    (hwv : ∀ l < 2, ∀ e < 4, (word (u.lane w l) (4 * h + e)).toNat = (F[8 * j + 4 * l + e]!).val)
    (hin : InRegions u.wr (coeffAddr tP (8 * j)) 32) (hM : MemOk m₀ tP E F j u.mem) :
    WP isa (.block (finQ w op off)) u fun u' => MemOk m₀ tP E F (j + 1) u'.mem ∧
      u'.mem = u.mem.writeW (coeffAddr tP (8 * j)) (u'.ymm .xmm0) ∧ u'.gpr = u.gpr ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧ ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, u'.lane r l = u.lane r l := by
  refine WP.mono (finQ_ok hw0 hl hq (by rw [hrdi]; exact hin))
    fun u' ⟨hm, hd, hg, hrd, hwr, hmx, hlane⟩ => ⟨fun c hc => ?_, by rw [hm, hrdi], hg, hrd, hwr, hmx, hlane⟩
  rw [hm, hrdi, coeffAt_write256 _ _ (by omega_arith) _ hc]
  split
  · rename_i hr
    obtain ⟨l, e, hl', he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ c = 8 * j + 4 * l + e :=
      ⟨(c - 8 * j) / 4, (c - 8 * j) % 4, by omega_arith, by omega_arith, by omega_arith⟩
    refine ⟨fun _ => ?_, fun h' => absurd h' (by omega_arith)⟩
    obtain hrest := (hM _ hc).2 (by omega_arith)
    obtain ha : (dword (u.mem.readW (u.gpr .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e).toNat =
        (coeffAt m₀ tP (8 * j + 4 * l + e)).toNat := by
      rw [hrdi, YAddSub.lane_coeff _ _ _ _ _ he, hrest]
    obtain hb : (dword (XBinOp.eval xop (u.lane w l) (u.lane .xmm14 l)) e).toNat = (F[8 * j + 4 * l + e]!).val := by
      rw [hz l hl', hop _ e he, hwv l hl' e he]
    rw [show 8 * (4 * (8 * j + 4 * l + e - 8 * j)) = 8 * (16 * l + 4 * e) by omega_arith, extract_ymm _ _ hl' he,
      hd l hl' e he, add_lane (by rw [ha]; exact (hE _ hc).1) (by rw [hb]; exact (F[8 * j + 4 * l + e]!).isLt), ha, hb,
      add_get _ _ (by rw [n_eq]; exact hc), val_add, (hE _ hc).2]
  · rename_i hr
    exact ⟨fun h' => (hM c hc).1 (by omega_arith), fun h' => (hM c hc).2 (by omega_arith)⟩

/-- `vpunpcklwd ymm10, ymm8, ymm9` and `vpunpckhwd ymm11, ymm8, ymm9`, in a lane. -/
theorem unpk2_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm10 .xmm8, xb .punpcklwd .xmm10 .xmm9, xb .movdqa .xmm11 .xmm8,
        xb .punpckhwd .xmm11 .xmm9]) t fun t' =>
      (t'.xmm .xmm10 = XBinOp.eval .punpcklwd (t.xmm .xmm8) (t.xmm .xmm9) ∧
        t'.xmm .xmm11 = XBinOp.eval .punpckhwd (t.xmm .xmm8) (t.xmm .xmm9)) ∧ XOnly [.xmm10, .xmm11] t t' := by
  simp only [xb]
  vrun [eval_movdqa]
  exact ⟨trivial, by xonly⟩

theorem lane_unpk2 : laneSseBlock [yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] =
    some [xb .movdqa .xmm10 .xmm8, xb .punpcklwd .xmm10 .xmm9, xb .movdqa .xmm11 .xmm8,
      xb .punpckhwd .xmm11 .xmm9] := by
  decide +kernel

/-- Word `4(q mod 2) + e` of `L` (`q < 2`) or `H`, the `vpunpck{l,h}wd` of
lanes `A` and `B` holding the words of the accumulator's coefficients of
iteration `i` (`accIdx`): coefficient `8(4i + q) + 4l + e`. -/
theorem wv_of_w {F : Poly} {i : Nat} {A B : BitVec 128} {l : Nat} (hl : l < 2)
    (hw : ∀ h < 2, ∀ k < 8, (word (if h = 0 then A else B) k).toNat = (F[accIdx (32 * i + 16 * h + 8 * l + k)]!).val)
    {q : Nat} (hq : q < 4) {e : Nat} (he : e < 4) :
    (word (if q < 2 then XBinOp.eval .punpcklwd A B else XBinOp.eval .punpckhwd A B) (4 * (q % 2) + e)).toNat =
      (F[8 * (4 * i + q) + 4 * l + e]!).val := by
  obtain hs := srcF_ok q hq l hl e he
  obtain hidx : 32 * i + 16 * (e % 2) + 8 * l + (2 * q + e / 2) = 32 * i + srcF q l e := by unfold srcF; omega_arith
  obtain hacc : accIdx (32 * i + srcF q l e) = 8 * (4 * i + q) + 4 * l + e := by
    rw [accIdx_add32 hs.1, hs.2]; omega_arith
  by_cases hq2 : q < 2
  · rw [ifp hq2]
    simp (disch := omega_arith) only [word_punpcklwd]
    obtain h1 : (if (4 * (q % 2) + e) % 2 = 0 then word A ((4 * (q % 2) + e) / 2) else word B ((4 * (q % 2) + e) / 2)) =
        word (if e % 2 = 0 then A else B) (2 * q + e / 2) := by
      rcases (by omega_arith : e % 2 = 0 ∨ e % 2 = 1) with h | h
      · rw [ifp (by omega_arith), ifp h]; exact congrArg _ (by omega_arith)
      · rw [ifn (by omega_arith), ifn (by omega_arith)]; exact congrArg _ (by omega_arith)
    rw [h1, hw _ (by omega_arith) _ (by omega_arith), hidx, hacc]
  · rw [ifn hq2]
    simp (disch := omega_arith) only [word_punpckhwd]
    obtain h1 : (if (4 * (q % 2) + e) % 2 = 0 then word A (4 + (4 * (q % 2) + e) / 2)
        else word B (4 + (4 * (q % 2) + e) / 2)) = word (if e % 2 = 0 then A else B) (2 * q + e / 2) := by
      rcases (by omega_arith : e % 2 = 0 ∨ e % 2 = 1) with h | h
      · rw [ifp (by omega_arith), ifp h]; exact congrArg _ (by omega_arith)
      · rw [ifn (by omega_arith), ifn (by omega_arith)]; exact congrArg _ (by omega_arith)
    rw [h1, hw _ (by omega_arith) _ (by omega_arith), hidx, hacc]

/-- Word `4(q mod 2) + e` of lane `l` of `L` (`q < 2`) or `H`, from the two
loads of iteration `i`: the accumulator's word of coefficient
`8(4i + q) + 4l + e`. -/
theorem wv_of {m : Mem} {aP : Addr} {F : Poly} (hF : Acc16 m aP F) {i : Nat} (hi : i < 8) {A B : BitVec 128}
    {l : Nat} (hl : l < 2)
    (hA : A = m.readW (wAddr aP (32 * i) + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
    (hB : B = m.readW (wAddr aP (32 * i) + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
    {q : Nat} (hq : q < 4) {e : Nat} (he : e < 4) :
    (word (if q < 2 then XBinOp.eval .punpcklwd A B else XBinOp.eval .punpckhwd A B) (4 * (q % 2) + e)).toNat =
      (F[8 * (4 * i + q) + 4 * l + e]!).val :=
  wv_of_w hl (fun h hh k hk => by
    rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
    · rw [ifp rfl, hA, show (BitVec.ofNat 64 0 : BitVec 64) = BitVec.ofNat 64 (32 * 0) from rfl,
        acc_word _ _ _ _ _ hk]; exact hF _ (by omega_arith)
    · rw [ifn (by decide), hB, show (BitVec.ofNat 64 32 : BitVec 64) = BitVec.ofNat 64 (32 * 1) from rfl,
        acc_word _ _ _ _ _ hk]; exact hF _ (by omega_arith)) hq he

theorem rdi_q (p : Addr) (i q off : Nat) (h : off = 32 * q) :
    coeffAddr p (32 * i) + BitVec.ofNat 64 off = coeffAddr p (8 * (4 * i + q)) := by
  subst h; rw [show 32 * q = 4 * (8 * q) by omega_arith, coeffAddr_off]; exact congrArg _ (by omega_arith)

/-- After `i` iterations, with `F` the accumulator. -/
structure Inv (s₀ : State) (F : Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (32 * i)
  rsi : s.gpr .rsi = wAddr (s₀.gpr .rsi) (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qD
  z : ∀ l < 2, s.lane .xmm14 l = 0
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  mem : MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F (4 * i) s.mem

section
variable {s₀ : State} (hp : (finK accY).pre s₀) {F : Poly} (hF : Acc16 s₀.mem (s₀.gpr .rsi) F)
include hp hF

omit hF in
theorem hE : ∀ c < 256, (coeffAt s₀.mem (s₀.gpr .rdi) c).toNat < q ∧
    ((polyAt s₀.mem (s₀.gpr .rdi))[c]!).val = (coeffAt s₀.mem (s₀.gpr .rdi) c).toNat := fun c hc =>
  ⟨hp.2.2.2.2.2.1 c (by rw [n_eq]; exact hc), polyAt_val hp.2.2.2.2.2.1 (by rw [n_eq]; exact hc)⟩

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ F i s) :
    WP isa (.block (finAccBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ F (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain hwT : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  obtain hrA : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  obtain hFs : Acc16 s.mem (s₀.gpr .rsi) F :=
    accY.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.2.2.1.symm) hF
  obtain r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 0) 32 :=
    ⟨_, hrA, by rw [hI.rsi, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 32) 32 :=
    ⟨_, hrA, by rw [hI.rsi, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
                exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [show finAccBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [.vmovdquLoad .l256 .xmm8 (at_ .rsi 0)] ++ ([.vmovdquLoad .l256 .xmm9 (at_ .rsi 32)] ++
        ([yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] ++
        (finQ .xmm10 .vpunpcklwd 0 ++ (finQ .xmm10 .vpunpckhwd 32 ++ (finQ .xmm11 .vpunpcklwd 64 ++
        (finQ .xmm11 .vpunpckhwd 96 ++ ([.alu .add .rsi (.imm 64), .alu .add .rdi (.imm 128),
          .alu .sub .rcx (.imm 1)] : List Instr))))))) from rfl, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L8, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L9, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_unpk2 (P := fun l t =>
      t.xmm .xmm10 = XBinOp.eval .punpcklwd ((s2.proj l).xmm .xmm8) ((s2.proj l).xmm .xmm9) ∧
      t.xmm .xmm11 = XBinOp.eval .punpckhwd ((s2.proj l).xmm .xmm8) ((s2.proj l).xmm .xmm9))
    fun l _ => unpk2_ok _) fun s3 ⟨U3, o3⟩ => ?_
  obtain o13 := (o1.trans o2).trans o3
  -- the words of `L` and `H`
  obtain hLH : ∀ q < 4, ∀ l < 2, ∀ e < 4,
      (word (if q < 2 then s3.lane .xmm10 l else s3.lane .xmm11 l) (4 * (q % 2) + e)).toNat =
        (F[8 * (4 * i + q) + 4 * l + e]!).val := by
    intro q hq l hl e he
    obtain e10 : s3.lane .xmm10 l = XBinOp.eval .punpcklwd (s2.lane .xmm8 l) (s2.lane .xmm9 l) := by
      rw [← State.proj_xmm, (U3 l hl).1, State.proj_xmm, State.proj_xmm]
    obtain e11 : s3.lane .xmm11 l = XBinOp.eval .punpckhwd (s2.lane .xmm8 l) (s2.lane .xmm9 l) := by
      rw [← State.proj_xmm, (U3 l hl).2, State.proj_xmm, State.proj_xmm]
    obtain hA : s2.lane .xmm8 l = s.mem.readW (wAddr (s₀.gpr .rsi) (32 * i) + BitVec.ofNat 64 0 +
        BitVec.ofNat 64 (16 * l)) 128 := by rw [o2.lane _ (by decide) l hl, L8 l hl, hI.rsi]
    obtain hB : s2.lane .xmm9 l = s.mem.readW (wAddr (s₀.gpr .rsi) (32 * i) + BitVec.ofNat 64 32 +
        BitVec.ofNat 64 (16 * l)) 128 := by rw [L9 l hl, o1.mem, o1.gpr, hI.rsi]
    have := wv_of hFs hi hl hA hB hq he
    by_cases hq2 : q < 2
    · rw [ifp hq2] at this ⊢; rw [e10]; exact this
    · rw [ifn hq2] at this ⊢; rw [e11]; exact this
  obtain hz3 : ∀ l < 2, s3.lane .xmm14 l = 0 := fun l hl => by rw [o13.lane _ (by decide) l hl]; exact hI.z l hl
  obtain hq3 : ∀ l < 2, s3.lane .xmm15 l = qD := fun l hl => by rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  obtain hrdi3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (32 * i) := by rw [o13.gpr, hI.rdi]
  obtain hw3 : s3.wr = s₀.wr := by rw [o13.wr, hI.wr]
  obtain hM3 : MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F (4 * i + 0) s3.mem := by
    rw [o13.mem]; exact hI.mem
  obtain inT : ∀ q < 4, InRegions s₀.wr (coeffAddr (s₀.gpr .rdi) (8 * (4 * i + q))) 32 := fun q hq => by
    rw [hp.2.1]; exact YAddSub.in32 (List.mem_singleton_self _) (by omega_arith)
  obtain hop0 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpcklwd a 0) e).toNat = (word a (4 * 0 + e)).toNat :=
    fun a e he => by have := dword_unpk0 a (h := 0) (by decide) he; rwa [ifp rfl] at this
  obtain hop1 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpckhwd a 0) e).toNat = (word a (4 * 1 + e)).toNat :=
    fun a e he => by have := dword_unpk0 a (h := 1) (by decide) he; rwa [ifn (by decide)] at this
  -- coefficients `32i, …, 32i + 7`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm10) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * i + 0) (by omega_arith) (by rw [hrdi3]; exact rdi_q _ _ _ _ rfl) hq3 hz3
    (fun l hl e he => by have := hLH 0 (by decide) l hl e he; rwa [ifp (by decide)] at this)
    (by rw [hw3]; exact inT 0 (by decide)) hM3) fun s4 ⟨M4, m4, g4, rd4, wr4, x4, ln4⟩ => ?_
  -- `32i + 8, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm10) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * i + 1) (by omega_arith) (by rw [g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 1 (by decide) l hl e he; rw [ifp (by decide)] at this; rw [ln4 _ (by decide) l hl]; exact this)
    (by rw [wr4, hw3]; exact inT 1 (by decide)) M4) fun s5 ⟨M5, m5, g5, rd5, wr5, x5, ln5⟩ => ?_
  -- `32i + 16, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm11) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * i + 2) (by omega_arith) (by rw [g5, g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 2 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact this)
    (by rw [wr5, wr4, hw3]; exact inT 2 (by decide)) M5) fun s6 ⟨M6, m6, g6, rd6, wr6, x6, ln6⟩ => ?_
  -- `32i + 24, …`
  rw [WP.block_append_iff]
  refine WP.mono (finQ_step (hE hp) (w := .xmm11) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * i + 3) (by omega_arith) (by rw [g6, g5, g4, hrdi3]; exact rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hq3 l hl)
    (fun l hl => by rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact hz3 l hl)
    (fun l hl e he => by
      have := hLH 3 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln6 _ (by decide) l hl, ln5 _ (by decide) l hl, ln4 _ (by decide) l hl]; exact this)
    (by rw [wr6, wr5, wr4, hw3]; exact inT 3 (by decide)) M6) fun s7 ⟨M7, m7, g7, rd7, wr7, x7, ln7⟩ => ?_
  obtain g37 : s7.gpr = s.gpr := by rw [g7, g6, g5, g4, o13.gpr]
  obtain l37 : ∀ r, r ∉ [XReg.xmm0, .xmm1] → ∀ l < 2, s7.lane r l = s3.lane r l := fun r hr l hl => by
    rw [ln7 r hr l hl, ln6 r hr l hl, ln5 r hr l hl, ln4 r hr l hl]
  obtain sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  obtain sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  obtain cT : ∀ q < 4, (pR (s₀.gpr .rdi)).Contains (coeffAddr (s₀.gpr .rdi) (8 * (4 * i + q))) 32 := fun q hq =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  vrunm [sx64, sx128]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g37, hI.rdi, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g37, hI.rsi, wAddr_add, Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [rd7, rd6, rd5, rd4, o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [wr7, wr6, wr5, wr4, hw3]
  · simp only [lane_setReg, lane_setFlags]; rw [l37 _ (by decide) l hl]; exact hq3 l hl
  · simp only [lane_setReg, lane_setFlags]; rw [l37 _ (by decide) l hl]; exact hz3 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m7, m6, m5, m4, o13.mem]
    exact (((hI.frame.writeW (List.mem_singleton_self _) _ (cT 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cT 1 (by decide))).writeW (List.mem_singleton_self _) _
      (cT 2 (by decide))).writeW (List.mem_singleton_self _) _ (cT 3 (by decide))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [show 4 * (i + 1) = 4 * i + 3 + 1 by omega_arith]; exact M7
  · rw [g37]
  · rw [g37]

end

/-- `pxor xmm14, xmm14`. -/
theorem zero14_ok (t : State) :
    WP isa (.block [xb .pxor .xmm14 .xmm14]) t fun t' => t'.xmm .xmm14 = 0 ∧ XOnly [.xmm14] t t' := by
  simp only [xb]
  vrun
  exact ⟨pxor_self _, by xonly⟩

end FinY

theorem finAccY_correct (s₀ : State) (hs : (finK accY).pre s₀) :
    ∃ t s', Exec isa finAccY s₀ t s' ∧ abiPreserved s₀ s' ∧ (finK accY).post s₀ s' := by
  obtain ⟨F0, hF0⟩ := hs.2.2.2.2.2.2
  obtain hW : WP isa finAccY s₀ fun s' => Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧
      FinY.MemOk s₀.mem (s₀.gpr .rdi) (polyAt s₀.mem (s₀.gpr .rdi)) F0 (4 * 8) s'.mem := by
    unfold finAccY
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, lo⟩ => ?_
    refine WP.mono (ylanes (vs := [yb .vpxor .xmm14 .xmm14 .xmm14]) (by decide +kernel)
      (P := fun _ t => t.xmm .xmm14 = 0) fun l _ => FinY.zero14_ok _) fun w2 ⟨Z2, o2⟩ => ?_
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (FinY.Inv s₀ F0) (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), o2.gpr, k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.gpr (by decide), o2.gpr, k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, o2.rd, k1.2.1], by rw [o.keep.2.2, o2.wr, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w2.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy],
            o2.lane _ (by decide) l hl, lq l hl]; decide,
        fun l hl => by
          rw [show u.lane .xmm14 l = w2.lane .xmm14 l by simp only [State.lane]; rw [o.xmm, hy],
            ← State.proj_xmm]; exact Z2 l hl,
        by rw [o.mem, o2.mem, m1]; exact Frame.refl _ _,
        fun c _ => ⟨fun h => absurd h (by omega_arith), fun _ => by rw [o.mem, o2.mem, m1]⟩⟩)
      fun i hi u hI => FinY.step hs hF0 hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, hI.mem⟩
  obtain ⟨t, s', he, ⟨hf, hM⟩, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rcx] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_),
    fun F hF => ?_⟩
  · simpa using hs.2.2.2.1
  · rw [acc16_unique hF hF0]
    exact polyIs_of_toNat fun c hc => (hM c (by rw [n_eq] at hc; exact hc)).1 (by rw [n_eq] at hc; omega_arith)


end VG.Proof.MlKem.X86_64
