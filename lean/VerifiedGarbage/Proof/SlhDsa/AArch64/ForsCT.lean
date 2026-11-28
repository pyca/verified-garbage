module

-- separate module: `forsSign`'s frames, a state of its precondition, and `T_k` of the roots in two runs, which `forsPk`'s proof shares

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTLeaf
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign` is constant time, and `Verified`

Its code has no frames and no depth, and what the cleanup of its callers
needs (`fors_side`); a state satisfies its precondition (`forsSat_pre`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase

variable {p : Params}

/-! ## Frames, depth, and the cleanup's side conditions -/

theorem fors_noFrames (L : Layout) (a k : Nat) (t4name ln : String) {t4 : Prog isa} (hT : t4.noFrames = true)
    (hL : (Impl.SlhDsa.AArch64.Tree.levels L t4name t4).noFrames = true) :
    (Impl.SlhDsa.AArch64.Fors.forsSign L a k t4name ln t4).noFrames = true := by
  simp only [Impl.SlhDsa.AArch64.Fors.forsSign, Impl.SlhDsa.AArch64.Fors.treeBody,
    Impl.SlhDsa.AArch64.Fors.subtreeBody, Impl.SlhDsa.AArch64.Fors.leafBody,
    Impl.SlhDsa.AArch64.Fors.subtreeHeights, Impl.SlhDsa.AArch64.Fors.topHeights,
    Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall]
  split <;> simp only [Code.noFrames, hT, hL, Bool.and_self]

theorem fors_depth (L : Layout) (a k : Nat) (t4name ln : String) {t4 : Prog isa} (hT : t4.aarch64Depth = 0)
    (hL : (Impl.SlhDsa.AArch64.Tree.levels L t4name t4).aarch64Depth = 0) :
    (Impl.SlhDsa.AArch64.Fors.forsSign L a k t4name ln t4).aarch64Depth = 0 := by
  simp only [Impl.SlhDsa.AArch64.Fors.forsSign, Impl.SlhDsa.AArch64.Fors.treeBody,
    Impl.SlhDsa.AArch64.Fors.subtreeBody, Impl.SlhDsa.AArch64.Fors.leafBody,
    Impl.SlhDsa.AArch64.Fors.subtreeHeights, Impl.SlhDsa.AArch64.Fors.topHeights,
    Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall]
  split <;> simp only [Code.aarch64Depth, hT, hL, Nat.max_self]

/-- What the cleanup of `forsSign`'s callers needs of its code (`Scrub.sideAll`). -/
theorem fors_side (hz : Sz p) (hA : As p) (t4name ln : String) (t4 : Prog isa)
    (hT : Scrub.sideAll (fun i => !i.writesDit) t4 = true)
    (hL : Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4) = true) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k t4name ln t4) =
      true := by
  simp only [Impl.SlhDsa.AArch64.Fors.forsSign, Impl.SlhDsa.AArch64.Fors.treeBody,
    Impl.SlhDsa.AArch64.Fors.subtreeBody, Impl.SlhDsa.AArch64.Fors.leafBody,
    Impl.SlhDsa.AArch64.Fors.subtreeHeights, Impl.SlhDsa.AArch64.Fors.topHeights,
    Impl.SlhDsa.AArch64.Fors.pkFors, Impl.SlhDsa.AArch64.thashCall]
  generalize Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name t4 = lv at hL ⊢
  have hl := hz.len
  generalize p.len = len at hl ⊢
  subst hl
  rcases hA with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> split <;> simp only [Scrub.sideAll, hT, hL, Bool.and_true, Bool.true_and] <;> decide

/-! ## A state satisfying the precondition -/

def fS : Addr := BitVec.ofNat 64 0x100000
def fSig : Addr := BitVec.ofNat 64 0x200000

/-- A state of the precondition: `scratch` and the signature apart, memory zero. -/
def forsSat (p : Params) : State where
  gpr r := match r with
    | .x0 => fS | .x1 => fSig | _ => 0
  sp := 0
  mem := fun _ => 0
  rd := []
  wr := [⟨fS, scratchLen⟩, ⟨fSig, p.forsSigLen⟩]

theorem bytes_zeroF (a : Addr) (n : Nat) : bytesAt (fun _ => 0) a n = List.replicate n 0 := by
  simp [bytesAt, List.map_const']

theorem forsSat_pre (hz : Sz p) (hA : As p) : (forsContract p).pre (forsSat p) := by
  have hn32 := hz.n32
  obtain ⟨-, -, ha, -, hk, -, -⟩ := hA.facts
  have hSL : p.forsSigLen ≤ 35 * 15 * 32 := by
    simp only [Params.forsSigLen]
    exact Nat.mul_le_mul (Nat.mul_le_mul hk (by omega)) hn32
  have eS : fS.toNat = 0x100000 := rfl
  have eG : fSig.toNat = 0x200000 := rfl
  refine ⟨⟨rfl, rfl, by show fS.toNat + scratchLen ≤ 2 ^ 64; rw [eS]; decide,
    by show fSig.toNat + p.forsSigLen ≤ 2 ^ 64; rw [eG]; omega, ?_,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, fun k _ => bytes_zeroF _ _, fun k _ => bytes_zeroF _ _,
      fun k _ => bytes_zeroF _ _, fun k _ => bytes_zeroF _ _⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  exact (Offset.disjoint_of_le (r₁ := ⟨fS, Layout.oSigTmp⟩) (r₂ := ⟨fSig, p.forsSigLen⟩)
    (by show fS.toNat + Layout.oSigTmp ≤ fSig.toNat; rw [eS, eG]; decide)
    (by show fSig.toNat + p.forsSigLen ≤ 2 ^ 64; rw [eG]; omega)).symm

/-! ## `T_k` of the roots, and the epilogue -/

/-- What `pkFors` needs. -/
structure PkPre (S : Addr) (sp : BitVec 64) (t : State) : Prop where
  x19 : t.gpr .x19 = S
  kp : (t.gpr .x20).toNat < 2 ^ 32
  scr : (⟨S, 65536⟩ : Region) ∈ t.wr
  fit : S.toNat + 65536 ≤ 2 ^ 64
  sp : t.sp = sp

theorem pkB_ok (hA : As p) : p.k * p.n + p.n + 32 ≤ Layout.strideB ∧ 0 < p.k := by
  rcases hA with ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ <;>
    rw [hn, hk] <;> decide

theorem PkPre.fields (hz : Sz p) {S : Addr} {sp : BitVec 64} {t : State} (h : PkPre S sp t) :
    WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
        Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .x20 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
        Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0)) t
      (PkPre S sp) := by
  rw [← List.append_nil (_ ++ Impl.SlhDsa.AArch64.setField _ _ 0)]
  exact pkFields_ok hz.n32 hz.n8 h.x19 h.kp h.scr fun t₁ k₁ _ _ => WP.block_nil
    ⟨by rw [k₁.get .x19, h.x19], by rw [k₁.get .x20]; exact h.kp, by rw [k₁.wr]; exact h.scr, h.fit,
      by rw [k₁.sp, h.sp]⟩

/-- `pkFors` and the epilogue, in two runs with `scratch` in `x19` and the
same stack pointer. -/
theorem pk_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String) {S : Addr} {sp : BitVec 64} :
    RelCT isa (fun a b => PkPre S sp a ∧ PkPre S sp b)
      (.seq (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code)
        (.block (Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Fors.saved))) fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  obtain ⟨hk, hk0⟩ := pkB_ok hA
  have eSB : Layout.strideB = 2208 := rfl
  have hB : ∀ t, PkPre S sp t → WP isa (Impl.SlhDsa.AArch64.Fors.pkFors ⟨p.n, p.len⟩ p.k name T.code) t
      fun w => w.gpr .x19 = S ∧ w.sp = sp := fun t ht =>
    pk_ok hz T name hk hk0 ht.x19 ht.kp ht.scr ht.fit fun t' _ _ hs g _ _ _ =>
      ⟨by rw [g .x19 (by decide) (by decide), ht.x19], by rw [hs, ht.sp]⟩
  refine relSeq (B₁ := fun w => w.gpr .x19 = S ∧ w.sp = sp) (B₂ := fun w => w.gpr .x19 = S ∧ w.sp = sp) ?_ hB hB
    (ct_epi fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2, hb.2], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]⟩)
  unfold Impl.SlhDsa.AArch64.Fors.pkFors
  refine relSeq (B₁ := PkPre S sp) (B₂ := PkPre S sp)
    (ct_pkFields hz hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.x19, hb.x19]⟩)
    (fun t ht => ht.fields hz) (fun t ht => ht.fields hz) ?_
  have hw : ∀ t, PkPre S sp t → WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oB
      Layout.strideB (p.n + 32 + p.k * p.n)) t fun w => w.gpr .x19 = S ∧ w.sp = sp := fun t ht =>
    WP.mono (tcall_wp T name ⟨p.n, p.len⟩ rfl hn32 (by decide) (by decide) (by decide) (by omega) (by
        rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod p.n]; simp [hn8]) (by omega) (by omega) ht.x19 ht.scr ht.fit)
      fun w ⟨hs, _, g⟩ => ⟨by rw [g .x19 (by decide) (by decide), ht.x19], by rw [hs, ht.sp]⟩
  refine relSeq (B₁ := fun w => w.gpr .x19 = S ∧ w.sp = sp) (B₂ := fun w => w.gpr .x19 = S ∧ w.sp = sp)
    ?_ hw hw (ct_pkCopy hz hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.2, hb.2], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]⟩)
  by_cases hS : ∃ u, PkPre S sp u
  · obtain ⟨u₀, hu₀⟩ := hS
    exact tcall_ct T name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsB hz hA h) (by decide) (by decide) (by decide)
      (by omega) (by rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod p.n]; simp [hn8]) (by omega) (by omega) hu₀.fit
      (fun a h => ⟨h.x19, h.scr⟩) (fun b h => ⟨h.x19, h.scr⟩) fun a b h h' => by rw [h.sp, h'.sp]
  · exact RelCT.of_false fun a b ⟨h, _⟩ => hS ⟨a, h⟩

end VG.Proof.SlhDsa.AArch64.Fors
