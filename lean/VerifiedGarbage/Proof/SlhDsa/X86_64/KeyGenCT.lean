module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
public meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on x86-64: key generation is constant time

Its two blocks by the taint analysis, with the pointers public, and the
call of `xmssTree` by its contract (`RelCT.call`), whose public data are
pointers too (`keyGen_ct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.KeyGen

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)

/-- The six SHAKE parameter sets. -/
abbrev Shake6 (p : Params) : Prop :=
  p = shake_128s ∨ p = shake_128f ∨ p = shake_192s ∨ p = shake_192f ∨ p = shake_256s ∨ p = shake_256f

theorem Shake6.sz {p : Params} (h : Shake6 p) : Wots4.Sz p := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem Shake6.hps {p : Params} (h : Shake6 p) : XmssTree.Hps p.hp := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Shake6.d {p : Params} (h : Shake6 p) : p.d - 1 < 2 ^ 31 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {P : State → State → Prop}

theorem ct_pro {p : Params} (hp : Shake6 p) (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rdi, .rcx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (proCode p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ hr (by taint_decide)

theorem ct_tail {p : Params} (hp : Shake6 p) (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r12, .r13], x.gpr r = y.gpr r) :
    RelCT isa P (.block (tailCode p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ hr (by taint_decide)

end

/-- After the call, in one run. -/
structure After (σ : State) (S : Addr) (w : State) : Prop where
  bx : w.gpr .rbx = S
  r12 : w.gpr .r12 = σ.gpr .rsi
  r13 : w.gpr .r13 = σ.gpr .rdx

theorem call_after {p : Params} (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) (T : Thash4Impl p.n)
    (t4name wn ln xn : String) {stack : Nat} (hst : T.stack + 32 ≤ stack) (hs63 : stack < 2 ^ 63)
    {σ : State} {S X : Addr} (hK : KG p stack σ) (hS : σ.gpr .rcx = S) {u : State} (hu : KPro p σ S X u) :
    WP isa (.call xn (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code)) u (After σ S) := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  obtain ⟨hpre, hc, hw⟩ := call_pre hz hh (by omega) hs63 hK hS hu
  exact XmssTree.xmsscall_ok hz T t4name wn ln xn (stack := stack - 8) (by omega) (by omega) hhp hhp9 hpre hc hw
    fun s' _ _ hcs _ _ _ => ⟨by rw [hcs _ (by decide), hu.bx], by rw [hcs _ (by decide), hu.r12],
      by rw [hcs _ (by decide), hu.r13]⟩

/-- `keyGen` is constant time: its timing depends only on the pointers. -/
theorem keyGen_ct {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 32 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ConstantTime isa (kgK p stack).pre (kgK p stack).pub (Impl.SlhDsa.X86_64.Shake.keyGen p f) := by
  have hz := hp.sz
  have hh := hp.hps
  have hd := hp.d
  have hn32 := hz.n32
  have hn8 := hz.n8
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have hK₁ : KG p stack s₁ := h₁
  have hK₂ : KG p stack s₂ := h₂
  obtain ⟨S, hS₁⟩ : ∃ S, s₁.gpr .rcx = S := ⟨_, rfl⟩
  have hS₂ : s₂.gpr .rcx = S := by rw [← p4, hS₁]
  have ent : ∀ {σ : State}, KG p stack σ → σ.gpr .rcx = S →
      WP isa (.block (proCode p)) σ (KPro p σ S (σ.gpr .rdi)) := fun {σ} hK hS =>
    pro_ok hn32 hn8 hd hS rfl (by rw [hK.wr, hS]; simp [scratchLen]) (by rw [hK.rd]; simp) hK.f_seed
      (by rw [← hS]; exact hK.d_seed_scr)
  have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
      Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
    rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.X86_64.Shake.keyGen p f) fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Shake.keyGen
    rw [hcode]
    refine Levels.relSeq (ct_pro hp fun x y ⟨hx, hy⟩ r hr => ?_) (fun x hx => by rw [hx]; exact ent hK₁ hS₁)
      (fun y hy => by rw [hy]; exact ent hK₂ hS₂) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx, hy, p1]
      · rw [hx, hy, p4]
    refine Levels.relSeq (RelCT.call (XmssTree.xmss_correct hz T f.t4name f.wotsName f.levelsName (stack := stack - 8)
        (by omega) (by omega) (by rcases hh with h | h | h | h <;> omega) (by rcases hh with h | h | h | h <;> omega))
      (XmssTree.xmss_ct hz T f.t4name f.wotsName f.levelsName (stack := stack - 8) (by omega) (by omega) hh)
      [] (callW p S) fun x y ⟨hx, hy⟩ => ?_)
      (fun x hx => call_after hz hh T _ _ _ _ hst hs63 hK₁ hS₁ hx)
      (fun y hy => call_after hz hh T _ _ _ _ hst hs63 hK₂ hS₂ hy) (ct_tail hp fun x y ⟨hx, hy⟩ r hr => ?_)
    · obtain ⟨q₁, c₁, w₁⟩ := call_pre hz hh (by omega) hs63 hK₁ hS₁ hx
      obtain ⟨q₂, c₂, w₂⟩ := call_pre hz hh (by omega) hs63 hK₂ hS₂ hy
      refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂, by rw [hx.sp, hy.sp, p5]⟩
      simp only [xmssContract, State.withRegions_gpr]
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
        State.callEntry_gpr _ (by decide), State.callEntry_rsp, State.callEntry_rsp, hx.rdi, hy.rdi, hx.rdx, hy.rdx,
        hx.sp, hy.sp, p5]
      exact ⟨rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.bx, hy.bx]
      · rw [hx.r12, hy.r12, p2]
      · rw [hx.r13, hy.r13, p3]
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The contract -/

/-- A state of `keyGenContract`'s precondition. -/
def kgSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => BitVec.ofNat 64 (2 ^ 64 - 16)
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 3 * p.n⟩]
  wr := [⟨0x2000, p.skLen⟩, ⟨0x3000, p.pkLen⟩, ⟨0x10000, scratchWords * 8⟩]

theorem kg_implies {p : Params} (hz : Wots4.Sz p) (n : Nat) (hs : n + 1 < 2 ^ 63) :
    (kgK p (n + 1)).Implies (Spec.SlhDsa.keyGenContract p X86_64.abi (n + 1)) := by
  have hn32 := hz.n32
  refine ⟨fun s h => ?_, fun s s' _ h => ?_, fun s₁ s₂ _ _ h => ?_, ⟨kgSat p, ?_⟩⟩
  · sig_pre [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, X86_64.abi, VG.X86_64.argRegs] at h
    sig_split h
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 _ a11 a12 a13 _ a15 a16 a17 a18 a19 a20
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a11, a12, a13, a15, a16, a17, a18, a19, a20, h⟩
  · sig_post [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  · sig_pub [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, -, hdi, hsi, hdx, hcx⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, hsp⟩
  · have hsk : p.skLen ≤ 128 := by simp only [Params.skLen]; omega
    have hpk : p.pkLen ≤ 64 := by simp only [Params.pkLen]; omega
    have hsw : scratchWords * 8 = 65536 := rfl
    sig_pre [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, X86_64.abi, VG.X86_64.argRegs, kgSat]
    have e1 : (0x1000 : Addr).toNat = 0x1000 := rfl
    have e2 : (0x2000 : Addr).toNat = 0x2000 := rfl
    have e3 : (0x3000 : Addr).toNat = 0x3000 := rfl
    have e4 : (0x10000 : Addr).toNat = 0x10000 := rfl
    have e5 : (BitVec.ofNat 64 (2 ^ 64 - 16)).toNat = 2 ^ 64 - 16 := rfl
    have e6 : (BitVec.ofNat 64 (2 ^ 64 - 16) - BitVec.ofNat 64 (n + 1)).toNat = 2 ^ 64 - 16 - (n + 1) := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e5, BitVec.toNat_ofNat]; omega), e5, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    sig_and_intros
    all_goals first
      | omega
      | (apply Offset.disjoint_of_le <;> dsimp only <;> omega)
      | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;> omega)

/-! ## `Verified` -/

/-- `vg_slhdsa_shake_*_keygen` for a SHAKE parameter set `p` and any
implementation `T` of `thash4` meets `keyGenContract` in constant time. -/
theorem keyGen_verified {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 32 ≤ stack) (hs63 : stack < 2 ^ 63) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Shake.keyGen p f) (Spec.SlhDsa.keyGenContract p X86_64.abi stack) := by
  obtain ⟨n, rfl⟩ : ∃ n, stack = n + 1 := ⟨stack - 1, by omega⟩
  exact Verified.of_correct (fun s h => keyGen_wp hp.sz hp.hps hp.d T ht hst hs63 h)
    (keyGen_ct hp T ht hst hs63) (kg_implies hp.sz n hs63)

end VG.Proof.SlhDsa.X86_64.KeyGen
